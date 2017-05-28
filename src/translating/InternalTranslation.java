package translating;

import parser.ParserHelper;
import pddlElements.*;
import planner.SATSolver;
import trapper.CausalGraph;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;

import org.sat4j.specs.TimeoutException;

/**
 * @author ignasi
 *
 */
public class InternalTranslation extends Translation{

	/**
	 *
	 */
	private ArrayList<Disjunction> list_disjunctions;
	private CausalGraph causal;
	private Domain domain_translated = new Domain();
	private Hashtable<String, Effect> deadends = new Hashtable<String, Effect>();
	private int i = 0;
	private Domain domain_to_translate;
	private ArrayList<Action> listAxioms = new ArrayList<Action>();
	private HashSet<String> usedAxioms = new HashSet<String>();
	private HashSet<String> uselessObs = new HashSet<String>();

	public InternalTranslation(Domain d, CausalGraph cg) {
		// 0 - Copy domain metadata
		causal = cg;
		domain_to_translate=d;
		//For tests: non-deterministic problems without uncertainty
		if(domain_to_translate.list_disjunctions.isEmpty()){
			domain_translated = domain_to_translate;
			return;
		}
		list_disjunctions = domain_to_translate.list_disjunctions;
		domain_translated.Name = domain_to_translate.Name;
		domain_translated.ProblemInstance = domain_to_translate.ProblemInstance;
		domain_translated.costFunction = domain_to_translate.costFunction;
		
		// 1 - Translate predicates (all)
		translatePredicates(domain_to_translate.predicates_grounded, domain_to_translate.predicates_invariants_grounded);
		// 2-Translate initial state
		translateInitialState(domain_to_translate.state);
		// 3 - Translate goal
		translateGoal(domain_to_translate.goalState);
		// 3.5 - Add deductive actions
		addDeductiveActions(domain_to_translate);
		// 4 - Translate actions
		translateActions(domain_to_translate.list_actions);
		// 5 - Add aditional actions
		//addContingentMergeActions(domain_to_translate);
		// 6 - Add tag refutation
		//addTagRefutation(domain_to_translate);
		// 8 - Add axioms
		addAxiomsActions(domain_to_translate);
		// 9 - Translate invariants
		translateInvariants(domain_to_translate);
		// 10 - Add tag maximal effects: called when actions are translated
		//addTagMaximalEffects(domain_to_translate);
	}

	private void addAxiomsActions(Domain domain_to_translate) {
		HashSet<Axiom> unusedAxioms = new HashSet<Axiom>();
		HashSet<Axiom> useless = new HashSet<Axiom>();
		for(Axiom a : domain_to_translate._Axioms){
			if(!usedAxioms.contains(a._Name)){
				unusedAxioms.add(a);
				for(String predicate : a._Body){
					if(uselessObs.contains(predicate)){
						useless.add(a);
						break;
					}
				}
			}
		}
		unusedAxioms.removeAll(useless);
		//Re group axioms with the same body!
		Hashtable<ArrayList<String>, ArrayList<Axiom>> conditions = new Hashtable<>();
		for(Axiom axiom : unusedAxioms){
			if(conditions.containsKey(axiom._Body)){
				ArrayList<Axiom> aux = new ArrayList<Axiom>(conditions.get(axiom._Body));
				aux.add(axiom);
				conditions.put(axiom._Body, aux);
			}else{
				ArrayList<Axiom> aux = new ArrayList<Axiom>();
				aux.add(axiom);
				conditions.put(axiom._Body, aux);
			}
		}
		int i = 0;
		for(ArrayList<String> key : conditions.keySet()){
			Action a = new Action();
			Effect e = new Effect();
			for(String b : key){
				a._precond.add("K" + b);
				addPredicate("K" + b);
			}
			for(Axiom ax : conditions.get(key)){
				for(String b : ax._Head){
					e._Effects.add("K" + b);
					addPredicate("K" + b);
				}
			}
			a._Effects.add(e);
			a.Name = "K-axiom-" + i;
			listAxioms.add(a);
			//System.out.println(a.ToString("not"));
			i++;
		}
		System.out.println("Done.");
	}

	private void translateInvariants(Domain domain_to_translate) {
		/*Enumeration<String> e = domain_to_translate.predicates_invariants
		while(e.hasMoreElements()){
			String invariant_pred = e.nextElement().toString();
			domain_translated.predicates_invariants.put("K" + invariant_pred, 1);
		}*/
		for(String invariant_pred : domain_to_translate.predicates_invariants){
			domain_translated.predicates_invariants.add("K" + invariant_pred);
		}
	}

	private void addDeductiveActions(Domain domain_to_translate) {
		int i=0;
		for(Disjunction disj: domain_to_translate.list_disjunctions){
			for(String predicate : disj.getIterator()){
				Axiom kAx1 = new Axiom();
				Axiom kAx2 = new Axiom();
				kAx1._Name = "invariant-at-least-one-" + i;
				i++;
				kAx2._Name = "invariant-at-most-one-" + i;
				i++;
				kAx1._Head.add(predicate);
				kAx2._Body.add(predicate);
				for(String p_opposed : disj.getIterator()){
					if(!p_opposed.equals(predicate)){
						kAx2._Head.add(ParserHelper.complement(p_opposed));
						kAx1._Body.add(ParserHelper.complement(p_opposed));
					}
				}
				domain_to_translate._Axioms.add(kAx1);
				domain_to_translate._Axioms.add(kAx2);
			}
		}
	}

	protected void translateActions(Hashtable<String, Action> list_actions) {
		Enumeration<String> e = list_actions.keys();
		while(e.hasMoreElements()){
			Action a = list_actions.get(e.nextElement().toString());
			//Effect complexEff;
			/*if((complexEff = isComplex(a))!=null){
				a._Effects.remove(a._Effects.indexOf(complexEff));
				translateDeadAction(a, complexEff);
			}*/
			if(a.IsObservation){
				@SuppressWarnings("unused")				
				Hashtable<String, HashSet<String>> entailedBy = getReasonedPredicates(a);
				if(entailedBy != null)	translateObservations(a, entailedBy);
			}else{
				Action a_translated = new Action();
				//Copying costs
				a_translated.cost = a.cost;
				a_translated.IsObservation = false;
				a_translated.Name = a.Name;
				//a_translated._precond.add("Knormal-execution");
				for(String precondition : a._precond){
					//Preconditions now are conditions of conditionals effects
					//TODO: add M-predicates
					a_translated._precond.add("K" + precondition);
				}
				if(a.deductive_action){
					a_translated.deductive_action = true;
				}
				if(a._IsConditionalEffect){
					a_translated._IsConditionalEffect = true;
				}
				for(Effect eff : a._Effects){
					/*if(!eff._Condition.isEmpty() && isImposibleConditions(eff._Condition)){
						continue;
					}*/
					a_translated._Effects.addAll(translateEffects(eff, a._precond));
				}
				domain_translated.list_actions.put(a_translated.Name, a_translated);
			}
		}
	}

	private ArrayList<Effect> translateEffects(Effect eff, ArrayList<String> _precond){
		ArrayList<Effect> returnList = new ArrayList<Effect>();
		if(eff._Condition.isEmpty()){
			Effect generalEffect = new Effect();
			for(String effect : eff._Effects){
				generalEffect._Effects.add("K" + effect);
				if(effect.startsWith("~")){
					generalEffect._Effects.add("~K" + effect.substring(1));
				}else{
					generalEffect._Effects.add("~K~" + effect);
					addPredicate("K" + ParserHelper.complement(effect));
				}
			}
			returnList.add(generalEffect);
		}else{
			Effect supportRule = new Effect();
			Effect cancelRule = new Effect();
			for(String condition : eff._Condition){			
				supportRule._Condition.add("K" + condition);
				addPredicate("K" + condition);
				cancelRule._Condition.add("~K" + ParserHelper.complement(condition));
				addPredicate("K" + ParserHelper.complement(condition));
			}
			for(String effect : eff._Effects){
				supportRule._Effects.add("K" + effect);
				//TODO: eliminate effects starting with ~:
				if(effect.startsWith("~")){
					supportRule._Effects.add("~K" + effect.substring(1));
				}else{
					supportRule._Effects.add("~K~" + effect);
					addPredicate("K" + ParserHelper.complement(effect));
				}
				addPredicate("K" + effect);
				cancelRule._Effects.add("~K" + ParserHelper.complement(effect));
				addPredicate("K" + ParserHelper.complement(effect));
			}
			returnList.add(supportRule);
			returnList.add(cancelRule);
		}
		return returnList;
	}

	private void translateObservations(Action a, Hashtable<String, HashSet<String>> deductions) {
		Action a_translated = new Action();
		a_translated.IsObservation = true;
		a_translated.Name = a.Name;
		a_translated.cost = a.cost;
		Effect e = new Effect();
		Branch b = new Branch();
		String newPrecond = "not-observed-" + a.Name;
		addPredicate(newPrecond);
		
		String observable = a._Effects.get(0)._Effects.get(0);

		domain_translated.state.put(newPrecond, 1);
		for(String precondition : a._precond){
			a_translated._precond.add("K" + precondition);
			a_translated._precond.add(newPrecond);
			//e._Condition.add("K" + precondition);
		}
		//An observation has only one observable literal:
		String obs = a._Effects.get(0)._Effects.get(0);
		String negObs = ParserHelper.complement(obs);

		Branch branch1 = new Branch();
		Branch branch2 = new Branch();

		addPredicate("K" + obs);
		addPredicate("K" + negObs);
		
		branch1._Branches.add("K" + observable);
		branch1._Branches.add("~K" + ParserHelper.complement(observable));
		branch2._Branches.add("K" + ParserHelper.complement(observable));
		branch1._Branches.add("~K" + observable);
		
		//Get all deducted literals for obs 1
		/*for(String deducted : deductions.get(obs)) {
			addPredicate("K" + deducted);
			addPredicate("K" + ParserHelper.complement(deducted));
			branch1._Branches.add("K" + deducted);
			branch1._Branches.add("~K" + ParserHelper.complement(deducted));
		}*/
		//Same for obs 2
		/*for(String deducted : deductions.get(negObs)){
			addPredicate("K" + deducted);
			addPredicate("K" + ParserHelper.complement(deducted));
			branch2._Branches.add("K" + deducted);
			branch2._Branches.add("~K" + ParserHelper.complement(deducted));
		}*/

		branch1._Branches.add("~" + newPrecond);
		branch2._Branches.add("~" + newPrecond);

		//a_translated._Effects.add(e);
		a_translated._Branches.add(branch1);
		a_translated._Branches.add(branch2);

		domain_translated.list_actions.put(a_translated.Name, a_translated);
		//createObsDetupAction(a);
	}

	@SuppressWarnings("unchecked")
	private Hashtable<String, HashSet<String>> getReasonedPredicates(Action a){
		/*An observation is invalid if:
		* 1- A branch of an observation entails an invalid state. Example, there are no wumpus when both outcomes
		* means a wumpus is near.
		* 2- There is no information added: an observation in a cell where there is no wumpus near.*/
		Hashtable<String, HashSet<String>> entailedBy = new Hashtable<String, HashSet<String>>();
		HashSet<String> used = new HashSet<String>();
		String predicate = a._Effects.get(0)._Effects.get(0);
		String negPredicate = ParserHelper.complement(a._Effects.get(0)._Effects.get(0));
		HashSet<String> tempUsed = (HashSet<String>) usedAxioms.clone();		
		entailedBy.put(predicate, fixedPointIterationReasoning(predicate, used));
		entailedBy.put(negPredicate, fixedPointIterationReasoning(negPredicate, used));		
		//Review conditions!  && validOutcome()
		//TODO: I need to cut actions that take off more than one disjunction: i mean 
		// eliminate actions that allow the agent to infer there is no wumpus anywere.
		if(((entailedBy.get(predicate).size()==1) && (entailedBy.get(negPredicate).size()==1)) || !validOutcome(negPredicate)){
			System.out.println("Useless observation: " + a.Name);
			usedAxioms.clear();
			uselessObs.add(predicate);
			//used.clear();
			return null;
		}
		usedAxioms.addAll(tempUsed);
		//usedAxioms.addAll(used);
		//System.out.println("Used axioms: " + used.toString());
		return entailedBy;
	}

	private boolean validOutcome(String negPredicate) {
		try {
			boolean r = domain_to_translate.sat.isSolvable(negPredicate);
			return r;
		} catch (TimeoutException e) {
			e.printStackTrace();
			return false;
		}
	}

	private HashSet<String> fixedPointIterationReasoning(String predicate, HashSet<String> used){
		HashSet<String> lit = new HashSet<String>();
		lit.add(predicate);
		boolean fix = false;
		while(!fix){
			HashSet<String> litAdded = new HashSet<String>(lit);
			for(Axiom ax : domain_to_translate._Axioms){
				if(entailedBy(litAdded, ax)){
					litAdded.addAll(ax._Head);
					//usedAxioms.add(ax._Name);
				}
			}
			/*domain_to_translate._Axioms.stream().filter(ax -> entailedBy(litAdded, ax._Body)).forEach(ax -> {
				litAdded.addAll(ax._Head);
				used.add(ax._Name);
			});*/
			if(lit.size() == litAdded.size()) fix = true;
			lit = litAdded;
		}
		return lit;
	}

	private boolean entailedBy(HashSet<String> litAdded, Axiom ax) {
		for(String s : ax._Body){
			if(!litAdded.contains(s)){
				return false;
			}
		}
		return true;
	}

	protected void translateGoal(ArrayList<String> goalState) {
		for(String predicate_goal : goalState){
			domain_translated.goalState.add("K" + predicate_goal);
			addPredicate("K" + predicate_goal);
		}
	}

	protected void translatePredicates(ArrayList<String> predicates_grounded, Hashtable<String, Integer> predicates_invariants_grounded) {
		//1- predicates without tags
		//addPredicate("Knormal-execution");
		//addPredicate("Kn_normal-execution");
		for(String predicate : predicates_grounded){
			if(!predicates_invariants_grounded.containsKey(predicate)){
				//KL
				addPredicate("K" + predicate);
				//K not L
				addPredicate("K~" + predicate);
			}					
		}
	}
	
	private void addPredicate(String predicate){
		if(!domain_translated.predicates_count.containsKey(predicate)){
			domain_translated.predicates_grounded.add(predicate);
			domain_translated.predicates_count.put(predicate, 1);
		}
	}

	protected void translateInitialState(Hashtable<String, Integer> state) {
		Enumeration<String> e = state.keys();
		//1-Add state 
		//domain_translated.state.put("Knormal-execution", 1);
		while(e.hasMoreElements()){
			String key_state = e.nextElement().toString();
			domain_translated.state.put("K" + key_state, 1);
			addPredicate("K" + key_state);
		}
	}

	public Domain getDomainTranslated() {
		return domain_translated;
	}

	public ArrayList<Action> getListAxioms() {
		return listAxioms;
	}
	
}