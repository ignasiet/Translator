package bdd;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import bdd.BDDAction;
import bdd.BDDUtils;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDVarSet;
import pddlElements.Action;
import pddlElements.Branch;
import pddlElements.Domain;
import pddlElements.Effect;

public class BDDSearcher {
	
	private Domain _Domain;
	private BDDUtils utils = new BDDUtils();
	private Integer lastUsed = 0;
	private BDD regressionFormula;
	private BDD goal = utils.one();
	private BDD initialState = utils.one();
	private Hashtable<String, Integer> var2num = new Hashtable<String, Integer>();
	private Hashtable<Integer, String> num2var = new Hashtable<Integer, String>();
	private ArrayList<BDDAction> actions = new ArrayList<BDDAction>();
	
	public BDDSearcher(Domain d) {
		_Domain = d;
		translateDomain2BDD();
		translateInitialState();
		translateGoalStates();
		BDD newBDD = goal;
		BDD lastBDD = null;
		while(!fixedPointComputation(newBDD, lastBDD)){
			lastBDD = newBDD;
			for(BDDAction a : actions){
				if(intersect(newBDD, a.effects)){
					BDD s = existencialQuantification(a.effects.and(newBDD), a);
					s = s.and(a.preconditions);
					if(!s.isZero()){
						newBDD = newBDD.or(s);
					}
				}
			}
		}
		regressionFormula = newBDD;
	}
	
	private boolean intersect(BDD a, BDD b){
		/*try{
			int[] x = a.toVarSet().toArray();
			int[] y = b.toVarSet().toArray();
			List<Integer> xList = new ArrayList<Integer>();
			List<Integer> yList = new ArrayList<Integer>();
		    for (int index = 0; index < x.length; index++){
		        xList.add(x[index]);
		    }
		    for (int index = 0; index < y.length; index++){
		        yList.add(y[index]);
		    }
			xList.retainAll(yList);
			return !xList.isEmpty();
		}catch(Exception e){
			//System.out.println("Error: " + e.getMessage());
			return false;
		}*/
		BDDVarSet x = a.toVarSet().intersect(b.toVarSet());
		if(!a.toVarSet().equals(x)){
			return false;
		}else{
			return true;
		}
	}
		
	private BDD existencialQuantification(BDD states, BDDAction action) {
		states = states.exist(action.effects.toVarSet());
		/*for (Integer change : action.modify) {
			BDD auxChange = utils.createTrueBDD(change);
			states = states.exist(auxChange);
		}*/
		return states;
	}
	
	private boolean fixedPointComputation(BDD newBDD, BDD lastBDD) {
		if(lastBDD == null){
			return false;
		}else{
			return newBDD.equals(lastBDD);
		}		
	}

	private void translateInitialState() {
		Enumeration<String> e = _Domain.state.keys();
		while(e.hasMoreElements()){
			String pred = e.nextElement().toString();
			initialState = initialState.and(createBDD(pred));
		}
	}

	private void translateGoalStates() {
		for(String goalPred : _Domain.goalState){
			goal = goal.and(createBDD(goalPred));
		}
	}

	private void translateDomain2BDD() {
		Enumeration<String> e = _Domain.list_actions.keys();
		while(e.hasMoreElements()){
			String actionName = e.nextElement().toString();
			Action a = _Domain.list_actions.get(actionName);
			if(!a.IsObservation){
				if(a._Effects.size() == 1){
					actions.add(translateSingleEffectAction(a));
				}else{
					actions.addAll(translateMultiEffectsAction(a));
				}
			}else{
				actions.addAll(translateObservation(a));
			}
		}
	}
	
	private ArrayList<BDDAction> translateObservation(Action a) {
		ArrayList<BDDAction> returnList = new ArrayList<BDDAction>();
		BDD BDDprec = preconditions2BDD(a);
		int i = 1;
		for(Branch b : a._Branches){
			BDDAction actionBDD = new BDDAction();
			actionBDD.Name = a.Name + "_Eff" + i;
			i++;
			actionBDD.preconditions = BDDprec;
			BDD eff = utils.one();
			for(String cond : b._Branches){
				eff = eff.and(createBDD(cond));
			}
			actionBDD.effects = eff;
			returnList.add(actionBDD);
		}
		return returnList;
	}

	private ArrayList<BDDAction> translateMultiEffectsAction(Action a) {
		ArrayList<BDDAction> returnList = new ArrayList<BDDAction>();
		BDD BDDprec = preconditions2BDD(a);
		int i = 1;
		for(Effect eff : a._Effects){
			BDDAction actionBDD = new BDDAction();
			actionBDD.Name = a.Name + "_Eff" + i;
			i++;
			actionBDD.preconditions = BDDprec;
			for(String cond : eff._Condition){
				actionBDD.preconditions = actionBDD.preconditions.and(createBDD(cond));
			}
			actionBDD.effects = effects2BDD(eff, actionBDD);
			returnList.add(actionBDD);
		}
		return returnList;
	}
	
	private BDDAction translateSingleEffectAction(Action a) {
		BDDAction actionBDD = new BDDAction();
		actionBDD.Name = a.Name;
		actionBDD.preconditions = preconditions2BDD(a);
		for(Effect e : a._Effects){
			if(!e._Condition.isEmpty()){
				for(String cond : e._Condition){
					actionBDD.preconditions.and(createBDD(cond));
				}
			}
			actionBDD.effects = effects2BDD(e, actionBDD);
		}
		return actionBDD;
	}
	
	private BDD effects2BDD(Effect e, BDDAction a) {
		BDD eff = utils.one();
		for(String effect : e._Effects){
			eff = eff.and(createBDD(effect));
			a.modify.add(getVar(effect));
		}
		return eff;
	}
	
	private BDD createBDD(String var){
		if(var.startsWith("~")){
			return utils.createFalseBDD(getVar(var.substring(1)));
		}else{
			return utils.createTrueBDD(getVar(var));
		}
	}
	
	private BDD preconditions2BDD(Action a){
		BDD prec = utils.one();
		for(String precondition : a._precond){
			setVar(precondition);
			BDD precond = utils.createTrueBDD(getVar(precondition));
			prec = prec.and(precond);
		}
		return prec;
	}
	
	private Integer getVar(String var){
		if(!var2num.containsKey(var)){
			var2num.put(var, lastUsed);
			num2var.put(lastUsed, var);
			lastUsed++;
		}
		return var2num.get(var);
	}
	
	private void setVar(String var){
		if(!var2num.containsKey(var)){
			var2num.put(var, lastUsed);
			num2var.put(lastUsed, var);
			lastUsed++;
		}
	}

	public BDD getRegressionFormula(){
		return regressionFormula;
	}
}
