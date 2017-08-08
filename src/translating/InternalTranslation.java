package translating;

import parser.ParserHelper;
import pddlElements.*;
import causalgraph.CausalGraph;

import java.util.*;

/**
 * @author ignasi
 *
 */
public class InternalTranslation extends Translation{

	private ArrayList<Disjunction> list_disjunctions;
	private CausalGraph causal;
	private Domain domain_translated = new Domain();
	private Hashtable<String, Effect> deadends = new Hashtable<String, Effect>();
	private int i = 0;
	private Domain domain_to_translate;
	private ArrayList<Action> listAxioms = new ArrayList<Action>();
	private HashSet<String> usedAxioms = new HashSet<String>();
	private HashSet<String> uselessObs = new HashSet<String>();
	private ArrayList<Action> ObsHeuristics = new ArrayList<Action>();
	private Hashtable<String, HashSet<String>> oppositeObs = new Hashtable<String, HashSet<String>>();
	private Hashtable<String, HashSet<String>> causes = new Hashtable<String, HashSet<String>>();

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
		renforceAxioms();
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

	private void addDeductiveActions(Domain domain_to_translate) {
		int i=0;
		for(Disjunction disj: domain_to_translate.list_disjunctions){
			for(String predicate : disj.getIterator()){
				//entailedBy.put(predicate, fixedPointIterationReasoning(predicate));
				Axiom kAx1 = new Axiom();
				Axiom kAx2 = new Axiom();
				kAx1._Name = "invariant-at-least-one-" + i;
				i++;
				kAx2._Name = "invariant-at-most-one-" + i;
				i++;
				kAx1._Head.add(predicate);
				kAx2._Body.add(predicate);
				if(domain_to_translate.isObservable(predicate)){
					kAx1._Body.add("not-observed-" + predicate);
					kAx1._Head.add("~not-observed-" + predicate);
				}
				//entailedBy.put(predicate, fixedPointIterationReasoning(predicate));
				for(String p_opposed : disj.getIterator()){
					if(!p_opposed.equals(predicate)){
						kAx2._Head.add(ParserHelper.complement(p_opposed));
						//kAx2._Head.add("~not-observed-" + p_opposed);
						kAx1._Body.add(ParserHelper.complement(p_opposed));
					}
				}
				domain_to_translate._Axioms.add(kAx1);
				domain_to_translate._Axioms.add(kAx2);
			}
		}
	}

	private void renforceAxioms(){
		ArrayList<ArrayList<String>> ruleSet = new ArrayList<ArrayList<String>>();
		for(ArrayList<String> preds : domain_to_translate.specialAxioms){
			//This is a special axioms inference...please refactor...seriously...
			if(preds.size() > 3){
				ruleSet.add(preds);
			}
			for(String predicate : preds){
				Axiom rule = new Axiom();
				rule._Body.add(predicate);
				for(String predOpposed : preds) {
					if (!predOpposed.equals(predicate)) {
						rule._Head.add(ParserHelper.complement(predOpposed));
					}
				}
				if(validOutcome(rule) || domain_to_translate.isObservable(rule._Body.get(0))){
					rule._Name = "extra-rule-" + predicate;
					domain_to_translate._Axioms.add(rule);
					if(domain_to_translate.isObservable(predicate)) createOpRule(ParserHelper.complement(predicate), rule._Head);
				}
			}
		}
		for(ArrayList<String> orRule : ruleSet){
			for(ArrayList<String> otherRule : ruleSet){
				if(orRule == otherRule) continue;
				ArrayList<String> auxRule = new ArrayList<>(otherRule);
				auxRule.retainAll(orRule);
				if(!auxRule.isEmpty()){
					mergeRules(orRule, otherRule, auxRule);
				}
			}
		}
	}

	private void createOpRule(String complement, ArrayList<String> head) {
		Axiom ax = new Axiom();
		ArrayList<ArrayList<String>> metaMerge = new ArrayList<ArrayList<String>>();
		for(String opposite : head){
			ArrayList<String> predicates = new ArrayList<String>();
			if(!domain_to_translate.ruleSet.containsKey(ParserHelper.complement(opposite))) continue;
			for(ArrayList<String> rules : domain_to_translate.ruleSet.get(ParserHelper.complement(opposite))){
				for(String p : rules){
					if(domain_to_translate.isObservable(p)) predicates.add(p);
				}
			}
			metaMerge.add(predicates);
		}
		boolean b = true;
		ArrayList<String> positiveDisj = new ArrayList<String>();
		for(ArrayList<String> list : metaMerge){
			if(b){
				positiveDisj.addAll(list);
				b = false;
			}else{
				positiveDisj.retainAll(list);
			}
		}
		if(positiveDisj.isEmpty()) return;
		if(positiveDisj.size() == 1 && positiveDisj.contains(complement)) return;
		ax._Name = "positive-obs-" + complement;
		ax._Body.add(complement);
		ax._Head.addAll(positiveDisj);
		domain_to_translate._Axioms.add(ax);
	}

	private void mergeRules(ArrayList<String> orRule, ArrayList<String> otherRule, ArrayList<String> auxRule) {
		Axiom ax = new Axiom();
		for(String observable : orRule){
			if(domain_to_translate.isObservable(observable)){
				ax._Body.add(ParserHelper.complement(observable));
			}
		}
		for(String observable : otherRule){
			if(domain_to_translate.isObservable(observable)){
				ax._Body.add(ParserHelper.complement(observable));
			}
		}
		for(String possiblePred : auxRule){
			for(Disjunction d : domain_to_translate.list_disjunctions){
				String keySafe = domain_to_translate.related.get(possiblePred).get(0);
				if(!d.contains(keySafe)) continue;
				for(String o : d.variablesDerivates.get(keySafe)){
					if(!o.equals(ParserHelper.complement(possiblePred))) ax._Head.add(o);
				}
			}
		}
		ax._Name = "merged-axiom-" + ax._Head.toString();
		domain_to_translate._Axioms.add(ax);
	}

	private ArrayList<Axiom> recycleRules(){
		Hashtable<ArrayList<String>, ArrayList<Axiom>> conditions = new Hashtable<ArrayList<String>, ArrayList<Axiom>>();
		for(Axiom a : domain_to_translate._Axioms){
			if(usedAxioms.contains(a._Name)){
				if(conditions.containsKey(a._Body)){
					ArrayList<Axiom> aSet = new ArrayList<Axiom>(conditions.get(a._Body));
					aSet.add(a);
					conditions.put(a._Body, aSet);
				}else{
					ArrayList<Axiom> aSet = new ArrayList<Axiom>();
					aSet.add(a);
					conditions.put(a._Body, aSet);
				}
			}
		}
		ArrayList<Axiom> returnedRules = new ArrayList<>();
		for(ArrayList<String> body : conditions.keySet()){
			Axiom rule = new Axiom();
			rule._Body.addAll(body);
			for(Axiom rules : conditions.get(body)){
				rule._Head.addAll(rules._Head);
			}
			returnedRules.add(rule);
		}
		return returnedRules;
	}

	private void addAxiomsActions(Domain domain_to_translate) {
		addSpecialAxioms();
		//Re group axioms with the same body!
		Hashtable<ArrayList<String>, ArrayList<Axiom>> conditions = new Hashtable<>();
		groupAxioms(conditions, removeUselessAxioms(), recycleRules());
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
					if(!e._Effects.contains("K" + b)){
						e._Effects.add("K" + b);
						e._Effects.add("~K" + ParserHelper.complement(b));
						if(domain_to_translate.isObservable(b)){
							e._Effects.add("K~not-observed-" + b.replace("~", ""));
							e._Effects.add("~Knot-observed-" + b.replace("~", ""));
						}
						addPredicate("K" + b);
					}if(domain_to_translate.UncertainPredicates.contains(b)){
						addCauses(b, ax._Body);
					}
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

	private void addSpecialAxioms(){
		for(Disjunction d : domain_to_translate.list_disjunctions){
			for(ArrayList<String> axiom : d.axioms){
				if(axiom.size()>2){
					for(String elem : axiom){
						Axiom a_1 = new Axiom();
						//Body: condition
						//Head: effect
						a_1._Body.add(elem);
						for(String other_elems : axiom){
							if(!other_elems.equals(elem)){
								a_1._Head.add(ParserHelper.complement(other_elems));
							}
						}
						domain_to_translate._Axioms.add(a_1);
					}
				}
			}
		}
	}

	private void addCauses(String b, ArrayList<String> body) {
		if(causes.containsKey(b)){
			HashSet<String> c = new HashSet<String>(causes.get(b));
			c.addAll(body);
			causes.put(b, c);
		}else{
			HashSet<String> c = new HashSet<String>(body);
			causes.put(b, c);
		}
	}

	private HashSet<Axiom> removeUselessAxioms(){
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
		return unusedAxioms;
	}

	//TODO: Refactor this...please!
	private void groupAxioms(Hashtable<ArrayList<String>, ArrayList<Axiom>> conditions, HashSet<Axiom> unusedAxioms, ArrayList<Axiom> axioms){
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
		for(Axiom rule :axioms){
			if(conditions.containsKey(rule._Body)){
				ArrayList<Axiom> aux = new ArrayList<Axiom>(conditions.get(rule._Body));
				aux.add(rule);
				conditions.put(rule._Body, aux);
			}else{
				ArrayList<Axiom> aux = new ArrayList<Axiom>();
				aux.add(rule);
				conditions.put(rule._Body, aux);
			}
		}
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

	private void addOppositeObs(String s, HashSet<String> orAxiom){
		if(oppositeObs.containsKey(s)){
			HashSet<String> oldAxiom = new HashSet<String>(orAxiom);
			oldAxiom.addAll(oppositeObs.get(s));
			oppositeObs.put(s, oldAxiom);
		}else {
			oppositeObs.put(s, orAxiom);
		}
	}

	private String oppositeObs(String predicate){
		String position = predicate.substring(predicate.indexOf("_"));
		for(String obs :domain_to_translate.observables){
			if(obs.contains(position)) return obs;
		}
		return null;
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
			}else if(a._IsNondeterministic){
				translateBranches(a);
			}else{
				Action a_translated = new Action();
				//Copying costs
				a_translated.cost = a.cost;
				a_translated.IsObservation = false;
				a_translated.Name = a.Name;
				for(String precondition : a._precond){
					//Preconditions now are conditions of conditionals effects
					a_translated._precond.add("K" + precondition);
				}
				if(a.deductive_action){
					a_translated.deductive_action = true;
				}
				if(a._IsConditionalEffect){
					a_translated._IsConditionalEffect = true;
				}
				for(Effect eff : a._Effects){
					a_translated._Effects.addAll(translateEffects(eff, a._precond));
				}
				domain_translated.list_actions.put(a_translated.Name, a_translated);
			}
		}
	}

	private void translateBranches(Action a) {
		Action a_translated = new Action();
		a_translated.Name = a.Name;
		
		for(String precondition : a._precond){
			a_translated._precond.add("K" + precondition);
		}
		
		Branch branch1 = new Branch();
		Branch branch2 = new Branch();
		if(!a._Effects.isEmpty()){
			for(String eff : a._Effects.get(0)._Effects){
				branch1._Branches.add("K" + eff);
				branch1._Branches.add("~K" + ParserHelper.complement(eff));
				branch2._Branches.add("K" + eff);
				branch2._Branches.add("~K" + ParserHelper.complement(eff));
			}
		}
		for(String br1 : a._Branches.get(0)._Branches){
			branch1._Branches.add("K" + br1);
			branch1._Branches.add("~K" + ParserHelper.complement(br1));
		}
		
		for(String br2 : a._Branches.get(1)._Branches){
			branch2._Branches.add("K" + br2);
			branch2._Branches.add("~K" + ParserHelper.complement(br2));
		}		
		a_translated._Branches.add(branch1);
		a_translated._Branches.add(branch2);
		domain_translated.list_actions.put(a_translated.Name, a_translated);
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

		//An observation has only one observable literal:
		String obs = a._Effects.get(0)._Effects.get(0);
		String negObs = ParserHelper.complement(obs);
		domain_to_translate.obsPredicates.add(obs);
		domain_to_translate.obsPredicates.add(negObs);

		String newPrecond = "Knot-observed-" + obs;
		String newNegatPrecond = "K~not-observed-" + obs;
		addPredicate(newPrecond);
		addPredicate(newNegatPrecond);

		domain_translated.state.put(newPrecond, 1);
		for(String precondition : a._precond){
			a_translated._precond.add("K" + precondition);
			a_translated._precond.add(newPrecond);
			//e._Condition.add("K" + precondition);
		}

		Branch branch1 = new Branch();
		Branch branch2 = new Branch();

		addPredicate("K" + obs);
		addPredicate("K" + negObs);

		if(oppositeObs.containsKey(negObs)){
			for(String p : oppositeObs.get(negObs)){
				branch2._Branches.add("K" + p);
				branch2._Branches.add("~K" + ParserHelper.complement(p));
				branch2._Branches.add("K~not-observed-" + p);
				branch2._Branches.add("~Knot-observed-" + p);
			}
		}
		
		//Get all deducted literals for obs 1
		for(String deducted : deductions.get(obs)) {
			addPredicate("K" + deducted);
			addPredicate("K" + ParserHelper.complement(deducted));
			branch1._Branches.add("K" + deducted);
			branch1._Branches.add("~K" + ParserHelper.complement(deducted));
			if(domain_to_translate.isObservable(deducted) && !obs.equals(deducted) && !negObs.equals(deducted)){
				branch1._Branches.add("K~not-observed-" + deducted.replace("~", ""));
				branch1._Branches.add("~Knot-observed-" + deducted.replace("~", ""));
			}
		}
		//Same for obs 2
		for(String deducted : deductions.get(negObs)){
			addPredicate("K" + deducted);
			addPredicate("K" + ParserHelper.complement(deducted));
			branch2._Branches.add("K" + deducted);
			branch2._Branches.add("~K" + ParserHelper.complement(deducted));
			if(domain_to_translate.isObservable(deducted) && !obs.equals(deducted) && !negObs.equals(deducted)){
				branch2._Branches.add("K~not-observed-" + deducted.replace("~", ""));
				branch2._Branches.add("~Knot-observed-" + deducted.replace("~", ""));
			}
		}

		branch1._Branches.add(newNegatPrecond);
		branch2._Branches.add(newNegatPrecond);
		branch1._Branches.add("~" + newPrecond);
		branch2._Branches.add("~" + newPrecond);


		createDeterminizedObs(a, a_translated._precond, branch1._Branches, branch2._Branches);
		//a_translated._Effects.add(e);
		a_translated._Branches.add(branch1);
		a_translated._Branches.add(branch2);
		//Falta adiciona quando é seguro!
		domain_translated.list_actions.put(a_translated.Name, a_translated);
		//createObsDetupAction(a);
	}

	private void createDeterminizedObs(Action a, ArrayList<String> precond, ArrayList<String> branches1, ArrayList<String> branches2) {
		//Add two heuristic actions that are the observations determinized
		Action obs1 = new Action();
		Action obs2 = new Action();
		obs1.Name = a.Name + "#1";
		obs2.Name = a.Name + "#2";
		obs1._precond.addAll(precond);
		obs2._precond.addAll(precond);

		Effect e1 = new Effect();
		Effect e2 = new Effect();

		//e1._Effects.add("K" + obs);
		//e1._Effects.add("~K" + negObs);
		e1._Effects.addAll(branches1);

		//e2._Effects.add("K" + negObs);
		//e2._Effects.add("~K" + obs);
		e2._Effects.addAll(branches2);

		obs1._Effects.add(e1);
		obs2._Effects.add(e2);

		ObsHeuristics.add(obs1);
		ObsHeuristics.add(obs2);
	}

	@SuppressWarnings("unchecked")
	private Hashtable<String, HashSet<String>> getReasonedPredicates(Action a){
		/*An observation is invalid if:
		* 1- A branch of an observation entails an invalid state. Example, there are no wumpus when both outcomes
		* means a wumpus is near.
		* 2- There is no information added: an observation in a cell where there is no wumpus near.*/
		Hashtable<String, HashSet<String>> entailedBy = new Hashtable<String, HashSet<String>>();
		//HashSet<String> used = new HashSet<String>();
		String predicate = a._Effects.get(0)._Effects.get(0);
		String negPredicate = ParserHelper.complement(a._Effects.get(0)._Effects.get(0));
		//HashSet<String> tempUsed = (HashSet<String>) usedAxioms.clone();

		HashSet<String> used = new HashSet<String>();
		entailedBy.put(predicate, fixedPointIterationReasoning(predicate, used));
		entailedBy.put(negPredicate, fixedPointIterationReasoning(negPredicate, used));

		if(((entailedBy.get(predicate).size()==1) && (entailedBy.get(negPredicate).size()==1)) ){
			System.out.println("Useless observation: " + a.Name);
			used.clear();
			uselessObs.add(predicate);
			return null;
		}
		usedAxioms.addAll(used);
		//System.out.println("Used axioms: " + used.toString());
		return entailedBy;
	}

	private boolean validOutcome(Axiom rule) {
		for(Disjunction d : domain_to_translate.list_disjunctions){
			if(d.derivates.containsAll(rule._Head)){
				return true;
			}
		}
		return false;
		/*for(String predicate : predicates){
			if(domain_to_translate.isObservable(predicate) && predicate.startsWith("~")) {
				HashMap<String, HashSet<String>> entailedBy = new HashMap<String, HashSet<String>>();
				ArrayList<String> addedAxioms = new ArrayList<String>();
				HashSet<String> used = new HashSet<String>();
				for(String predOpposed : predicates){
					if(!predOpposed.equals(predicate)){
						HashSet<String> list = fixedPointIterationReasoning(predOpposed, used);
						//usedAxioms.addAll(used);
						entailedBy.put(predOpposed, list);
						addedAxioms.addAll(list);
					}
				}
				for(Disjunction d : domain_to_translate.list_disjunctions){
					HashSet<String> orAxiom = new HashSet<String>();
					boolean init = false;
					for(String pred : entailedBy.keySet()){
						if(d.derivates.contains(pred)){
							if(!init){
								orAxiom.addAll(entailedBy.get(pred));
								init = true;
							}else {
								orAxiom.retainAll(entailedBy.get(pred));
							}
						}
					}
					if(d.violates(addedAxioms)){
						for(String s : domain_to_translate.opositeObs(predicate)) {
							addOppositeObs(s, orAxiom);
						}
					}
				}
			}
		}*/
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
					used.add(ax._Name);
				}
			}
			if(lit.size() == litAdded.size()) fix = true;
			lit = litAdded;
		}
		/*for(String b : lit){
			ArrayList<String> l = new ArrayList<String>();
			if(domain_to_translate.UncertainPredicates.contains(b)){
				l.add(predicate);
				addCauses(b, l);
			}
		}*/
		return lit;
	}

	private HashSet<String> fixedPointIterationReasoningArray(HashSet<String> predicates){
		HashSet<String> lit = new HashSet<String>();
		lit.addAll(predicates);
		boolean fix = false;
		while(!fix){
			HashSet<String> litAdded = new HashSet<String>(lit);
			for(Axiom ax : domain_to_translate._Axioms){
				if(entailedBy(litAdded, ax)){
					litAdded.addAll(ax._Head);
				}
			}
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

	public ArrayList<Action> getObsHeuristics() {
		return ObsHeuristics;
	}

}
