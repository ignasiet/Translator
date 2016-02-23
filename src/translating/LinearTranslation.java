package translating;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Enumeration;
import java.util.Hashtable;

import parser.ParserHelper;
import pddlElements.Action;
import pddlElements.Axiom;
import pddlElements.Branch;
import pddlElements.Disjunction;
import pddlElements.Domain;
import pddlElements.Effect;
import planner.CausalGraph;

/**
 * @author ignasi
 *
 */
public class LinearTranslation extends Translation{

	/**
	 * 
	 */
	private ArrayList<Disjunction> list_disjunctions;
	private CausalGraph causal;
	private Domain domain_translated = new Domain();
	private Hashtable<String, Effect> complexEffects = new Hashtable<String, Effect>();
	private Domain _Domain;
	
	public LinearTranslation(Domain domain_to_translate, CausalGraph cg) {
		// 0 - Copy domain metadata
		causal = cg;
		_Domain = domain_to_translate;
		list_disjunctions = domain_to_translate.list_disjunctions;
		domain_translated.Name = domain_to_translate.Name;
		domain_translated.ProblemInstance = domain_to_translate.ProblemInstance;
		// 1 - Translate predicates (all)
		translatePredicates(domain_to_translate.predicates_grounded, domain_to_translate.predicates_invariants_grounded);
		// 2-Translate initial state
		translateInitialState(domain_to_translate.state);
		// 3 - Translate goal
		translateGoal(domain_to_translate.goalState);
		// 4 - Translate actions
		translateActions(domain_to_translate.list_actions);
		// 5 - Add aditional actions
		//addContingentMergeActions(domain_to_translate);
		// 6 - Add tag refutation
		//addTagRefutation(domain_to_translate);
		// 7 - Add deductive actions
		addDeductiveActions(domain_to_translate);
		// 8 - Add axioms
		addAxiomsActions(domain_to_translate);
		// 9 - Translate invariants
		translateInvariants(domain_to_translate);
		// 10 - Add tag maximal effects: called when actions are translated
		//addTagMaximalEffects(domain_to_translate);
	}
	
	private Effect isComplex(Action a){
		if(a.IsObservation){
			return null;
		}
		for(Effect eff: a._Effects){
			for(String cond : eff._Condition){
				if(complexEffects.containsKey(cond.replace("~", ""))){
					return eff;
				}
				if(_Domain.isUncertainPredicate(cond.replace("~", ""))){
					System.out.println("Warning, uncertain cond in effect (not a simple problem): " + cond);
					complexEffects.put(cond.replace("~", ""), eff);
					return eff;
				}
			}
		}
		return null;
	}
	
	private boolean isDeadEndEffect(Effect eff){
		if(causal.isPossibleDeadEnd(eff)){
			System.out.println("Dead end effect (probably): ");
			System.out.println("Condition: " + eff._Condition.toString());
			System.out.println("Effects: " + eff._Effects.toString());
			//deadends.put(cond.replace("~", ""), eff);
			return true;
		}else{
			return false;
		}
	}

	private void translateInvariants(Domain domain_to_translate) {
		Enumeration<String> e = domain_to_translate.predicates_invariants.keys();
		while(e.hasMoreElements()){
			String invariant_pred = e.nextElement().toString();
			domain_translated.predicates_invariants.put("K" + invariant_pred, 1);
		}
	}

	private void addAxiomsActions(Domain domain_to_translate) {
		int i = 1;
		for(Axiom ax : domain_to_translate._Axioms){
			Action a = new Action();
			Axiom kAx = new Axiom();
			for(String prec : ax._Body){
				//Normal axiom action
				a._precond.add("K" + prec);
				kAx._Body.add("K" + prec);
				addPredicate("K" + prec);
			}
			for(String h : ax._Head){
				//Normal axiom action
				a._Effects.add(newEffect("K" + h));
				kAx._Head.add("K" + h);
				addPredicate("K" + h);
				if(h.startsWith("~")){
					//a.Name = i + "_deduct_not_" + h.substring(1);
					a.Name = "Closure_merge_imply_not_" + h.substring(1) + "_" + i;
				}else{
					//a.Name = i + "_deduct_" + h;
					a.Name = "Closure_merge_imply_" + h + "_" + i;
				}
			}
			domain_translated.list_actions.put(a.Name, a);
			domain_translated._Axioms.add(kAx);
			i++;
		}
	}
	
	private Effect newEffect(String eff){
		Effect e = new Effect();
		e._Effects.add(eff);
		return e;
	}

	private void addDeductiveActions(Domain domain_to_translate) {
		for(Disjunction disj: domain_to_translate.list_disjunctions){
			for(String predicate : disj.getIterator()){
				Action a = new Action();
				Action aInverted = new Action();
				//Axiom kAx1 = new Axiom();
				//Axiom kAx2 = new Axiom();
				a.Name = "Closure_merge_oneof-" + predicate;
				//kAx1._Name = a.Name;
				aInverted.Name = "Closure_merge_negate-oneof-" + predicate;
				//kAx2._Name = aInverted.Name;
				Effect kEffect = new Effect();
				Effect kEffectInverted = new Effect();
				kEffect._Effects.add("K" + predicate);
				//kAx1._Head.add("K" + predicate);
				aInverted._precond.add("K" + predicate);
				//kAx2._Body.add("K" + predicate);
				addPredicate("K" + predicate);
				for(String p_opposed : disj.getIterator()){
					if(!p_opposed.equals(predicate)){
						a._precond.add("K~" + p_opposed);
						kEffectInverted._Effects.add("K~" + p_opposed);
						addPredicate("K~" + p_opposed);
						//kAx2._Head.add("K~" + p_opposed);
						//kAx1._Body.add("K~" + p_opposed);
					}
				}
				a._Effects.add(kEffect);
				aInverted._Effects.add(kEffectInverted);
				a.deductive_action = true;
				aInverted.deductive_action = true;
				domain_translated.list_actions.put(a.Name, a);
				domain_translated.list_actions.put(aInverted.Name, aInverted);
				//domain_translated._Axioms.add(kAx1);
				//domain_translated._Axioms.add(kAx2);
			}
		}
	}

	protected void translateActions(Hashtable<String, Action> list_actions) {
		//TODO: test when Tags are needed
		Enumeration<String> e = list_actions.keys();
		while(e.hasMoreElements()){
			Action a = list_actions.get(e.nextElement().toString());
			Effect complexEff;
			if((complexEff = isComplex(a))!=null){
				if(isDeadEndEffect(complexEff)){
					a._Effects.remove(a._Effects.indexOf(complexEff));
					translateDeadAction(a, complexEff);
				}else{
					System.out.println("Houston, we have a problem!");
					addTagEffects(a);
					continue;
				}
			}
			if(a.IsObservation){
				translateObservations(a);
				continue;
			}else{
				Action a_translated = new Action();
				a_translated.IsObservation = false;
				a_translated.Name = a.Name;
				for(String precondition : a._precond){
					//Preconditions now are conditions of conditionals effects
					a_translated._precond.add("K" + precondition);
					if(!_Domain.state.containsKey(precondition.replace("~", "")) 
							&& (!_Domain.isUncertainPredicate(precondition.replace("~", "")))){
						domain_translated.state.put("K" + ParserHelper.complement(precondition.replace("~", "")), 1);
						addPredicate("K" + ParserHelper.complement(precondition.replace("~", "")));
					}
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
	
	private void addTagEffects(Action a) {
		Action a_translated = new Action();
		a_translated.IsObservation = false;
		a_translated.Name = a.Name;
		//actions with tags have no preconditions: all are moved to effects conditions
		// and for each effect we should have n*2 effects where n is the number of affected tags
		for(Effect effect : a._Effects){
			if(effect._Condition.isEmpty()){
				/*Effect e = new Effect();
				for(String eff : effect._Effects){
					e._Effects.add("K" + eff);
					addPredicate("K" + eff);
				}
				a_translated._Effects.add(e);*/
				ArrayList<String> emptyPreconditions = new ArrayList<>();
				for(Disjunction d : list_disjunctions){
					a_translated._Effects.addAll(translateTags(emptyPreconditions, effect, d));
				}
			}
			for(String cond : effect._Condition){				
				for(Disjunction d : list_disjunctions){
					createTagAction(d, cond);
					if(d.contains(cond)){
						a_translated._Effects.addAll(translateTags(a._precond, effect, d));
					}else{
						if(!_Domain.state.contains(cond.replace("~", ""))){
							domain_translated.state.put("K" + ParserHelper.complement(cond.replace("~", "")), 1);
							addPredicate("K" + ParserHelper.complement(cond.replace("~", "")));
						}
					}
				}
			}
		}
		domain_translated.list_actions.put(a_translated.Name, a_translated);
	}
	
	private void createTagAction(Disjunction d, String pred){
		pred = pred.replace("~", "");
		if(!domain_translated.list_actions.containsKey("Closure_Mergep_Tag_" + pred)){
			Action a = new Action();
			a.Name = "Closure_Mergep_Tag_" + pred;
			Effect e1 = new Effect();
			Effect e2 = new Effect();
			e1._Condition.add("K" + pred);
			e2._Condition.add("K" + ParserHelper.complement(pred));
			for(String tag : d.getIterator()){
				e1._Effects.add("K" + pred + "__" + tag);
				e2._Effects.add("K" + ParserHelper.complement(pred) + "__" + tag);
			}
			a._Effects.add(e1);
			a._Effects.add(e2);
			domain_translated.list_actions.put(a.Name, a);
		}		
	}	

	private ArrayList<Effect> translateTags(ArrayList<String> precond, Effect effect, Disjunction d) {
		ArrayList<Effect> returnList = new ArrayList<Effect>();
		//Tag 0:
		Effect support0 = new Effect();
		Effect cancel0 = new Effect();
		for(String prec : precond){
			support0._Condition.add("K" + prec);
			cancel0._Condition.add("~K" + ParserHelper.complement(prec));
			addPredicate("K" + prec);
			if(!_Domain.state.containsKey(prec.replace("~", ""))){
				domain_translated.state.put("K" + ParserHelper.complement(prec.replace("~", "")), 1);
			}
		}
		for(String cond : effect._Condition){
			support0._Condition.add("K" + cond);
			cancel0._Condition.add("~K" + ParserHelper.complement(cond));
			addPredicate("K" + cond);
		}
		for(String eff : effect._Effects){
			support0._Effects.add("K" + eff);
			cancel0._Effects.add("~K" + ParserHelper.complement(eff));
			addPredicate("K" + eff);
		}
		returnList.add(support0);
		returnList.add(cancel0);
		//
		for(String tag : d.getIterator()){
			Effect support = new Effect();
			Effect cancel = new Effect();
			for(String prec : precond){
				support._Condition.add("K" + prec + "__" + tag);
				cancel._Condition.add("~K" + ParserHelper.complement(prec) + "__" + tag);
				addPredicate("K" + prec + "__" + tag);
				if(!_Domain.state.contains(prec.replace("~", ""))){
					domain_translated.state.put("K" + ParserHelper.complement(prec.replace("~", "")) + "__" + tag, 1);
				}
			}
			for(String cond : effect._Condition){
				support._Condition.add("K" + cond + "__" + tag);
				cancel._Condition.add("~K" + ParserHelper.complement(cond) + "__" + tag);
				addPredicate("K" + cond + "__" + tag);
			}
			for(String eff : effect._Effects){
				support._Effects.add("K" + eff + "__" + tag);
				cancel._Effects.add("~K" + ParserHelper.complement(eff) + "__" + tag);
				addPredicate("K" + eff + "__" + tag);
			}
			returnList.add(support);
			returnList.add(cancel);
			//Add contingent merge!
			Action a1 = new Action();
			//Action a2 = new Action();
			a1.Name = "Closure_mergep_imply_deduct_" + tag;
			//a2.Name = "Closure_merge_imply_deduct_" + tag;
			Effect e1 = new Effect();
			//Effect e2 = new Effect();			
			for(String tag2 : d.getIterator()){	
				a1._precond.add("K" + tag + "__" + tag2);
				if(tag.equals(tag2)){
					domain_translated.state.put("K" + tag + "__" + tag2, 1);
					//a1._precond.add("K" + tag + "__" + tag2);
					//e2._Effects.add("K" + tag + "__" + tag2);
				}else{
					domain_translated.state.put("K" + ParserHelper.complement(tag) + "__" + tag2, 1);
					//a2._precond.add("K" + ParserHelper.complement(tag) + "__" + tag2);
				}
			}
			e1._Effects.add("K" + tag);
			a1._Effects.add(e1);
			//a2._Effects.add(e2);
			//Add contingent merge actions:
			domain_translated.list_actions.put(a1.Name, a1);
			//domain_translated.list_actions.put(a2.Name, a2);
		}
		return returnList;
	}

	private void translateActionCollectGoal(String pred){
		if(!domain_translated.list_actions.containsKey("Collect_Goal")){
			Action a = new Action();
			a.Name = "Collect_Goal";
			System.out.println("Creating action: " + a.Name);
			a._precond.add("K" + ParserHelper.complement(pred));
			Effect e = new Effect();
			for(String p : domain_translated.goalState){
				a._precond.add(p);
			}
			domain_translated.goalState.clear();			
			e._Effects.add("goal");
			domain_translated.goalState.add("goal");
			addPredicate("goal");
			a._Effects.add(e);
			domain_translated.list_actions.put(a.Name, a);
		}
	}
	
	private void translateDeadAction(Action oldAction, Effect complexEff) {
		Action a = new Action();
		String complexPrec = complexEff._Condition.get(0);
		oldAction._precond.add(ParserHelper.complement(complexPrec));
		complexPrec = complexPrec.substring(complexPrec.indexOf("_")+1);
		a.Name = "Closure_merge_imply_dead_" + complexPrec;
		System.out.println("Creating action: " + a.Name);
		for(Effect eff : oldAction._Effects){
			if(eff._Condition.isEmpty()){
				for(String e : eff._Effects){
					if(!e.startsWith("~")){
						a._precond.add("K" + e);
					}
				}
			}
		}
		for(String c : complexEff._Condition){
			a._precond.add("K" + c);
		}
		for(String h : complexEff._Effects){
			a._Effects.add(newEffect("K" + h));
			translateActionCollectGoal(h);
		}
		domain_translated.list_actions.put(a.Name, a);
	}
	
	private Disjunction needsEffectsTagMaximal(String predicate){
		Disjunction return_disj = new Disjunction();
		for(Disjunction disj : list_disjunctions){
			if(disj.contains(predicate)){
				return_disj = disj;
				return return_disj;
			}
		}
		return null;
	}
	
	private ArrayList<Effect> translateEffects(Effect eff, ArrayList<String> _precond){
		ArrayList<Effect> returnList = new ArrayList<Effect>();
		Effect supportRule = new Effect();
		Effect cancelRule = new Effect();
		for(String prec : _precond){
			supportRule._Condition.add("K" + prec);
			cancelRule._Condition.add("~K" + ParserHelper.complement(prec));
			addPredicate("K" + ParserHelper.complement(prec));
		}
		for(String condition : eff._Condition){			
			supportRule._Condition.add("K" + condition);
			addPredicate("K" + condition);
			cancelRule._Condition.add("~K" + ParserHelper.complement(condition));
			addPredicate("K" + ParserHelper.complement(condition));
		}
		for(String effect : eff._Effects){
			supportRule._Effects.add("K" + effect);
			if(effect.startsWith("~")){
				supportRule._Effects.add("~K" + effect.substring(1));
			}else{
				supportRule._Effects.add("~K~" + effect);
				addPredicate("K~" + ParserHelper.complement(effect));
			}
			addPredicate("K" + effect);
			cancelRule._Effects.add("~K" + ParserHelper.complement(effect));
			addPredicate("K" + ParserHelper.complement(effect));
		}
		returnList.add(supportRule);
		returnList.add(cancelRule);
		return returnList;
	}

	private void translateObservations(Action a) {
		//TODO: Add branches
		Action a_translated = new Action();
		a_translated.IsObservation = true;
		a_translated.Name = a.Name;
		Effect e = new Effect();
		for(String precondition : a._precond){
			a_translated._precond.add("K" + precondition);
			e._Condition.add("K" + precondition);
			e._Condition.add("~K" + ParserHelper.complement(precondition));
		}
		for(Effect e_action : a._Effects){
			Branch branch1 = new Branch();
			Branch branch2 = new Branch();
			for(String effect_result : e_action._Effects){
				a_translated._precond.add("~K" + ParserHelper.complement(effect_result));
				a_translated._precond.add("~K" + effect_result);
				e._Effects.add("K" + effect_result);
				addPredicate("K" + effect_result);
				addPredicate("K" + ParserHelper.complement(effect_result));
				e._Effects.add("K" + ParserHelper.complement(effect_result));
				branch1._Branches.add("K" + effect_result);
				branch1._Branches.add("~K" + ParserHelper.complement(effect_result));
				branch2._Branches.add("~K" + effect_result);
				branch2._Branches.add("K" + ParserHelper.complement(effect_result));
			}
			a_translated._Effects.add(e);
			a_translated._Branches.add(branch1);
			a_translated._Branches.add(branch2);
		}
		domain_translated.list_actions.put(a_translated.Name, a_translated);
	}

	protected void translateGoal(ArrayList<String> goalState) {
		for(String predicate_goal : goalState){
			domain_translated.goalState.add("K" + predicate_goal);
			addPredicate("K" + predicate_goal);
		}
	}

	protected void translatePredicates(ArrayList<String> predicates_grounded, Hashtable<String, Integer> predicates_invariants_grounded) {
		//1- predicates without tags
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
		while(e.hasMoreElements()){
			String key_state = e.nextElement().toString();
			domain_translated.state.put("K" + key_state, 1);
			addPredicate("K" + key_state);
		}
	}
	

	public Domain getDomainTranslated() {
		return domain_translated;
	}
	
}
