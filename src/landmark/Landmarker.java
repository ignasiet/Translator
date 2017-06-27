package landmark;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import pddlElements.*;
/**
 *
 * @author ignasi
 *
 */

public class Landmarker {

    private ArrayList<StepLandmark> _Steps = new ArrayList<StepLandmark>();
    private ArrayList<String> _Actions_list = new ArrayList<String>();
    private Hashtable<String, Action> _Actions = new Hashtable<String, Action>();
    private Hashtable<String, Integer> _State = new Hashtable<String, Integer>();
    //private Hashtable<String, Integer> _Invariants = new Hashtable<String, Integer>();
    private Hashtable<String, Integer> _GoalsAchieved = new Hashtable<String, Integer>();
    private ArrayList<String> _Goal = new ArrayList<String>();
    protected ArrayList<String> _Plan = new ArrayList<String>();
    protected Hashtable<Integer, ArrayList<String>> _ActionPlan = new Hashtable<Integer, ArrayList<String>>();
    protected Integer last_layer = 0;
    private ArrayList<String> landmarks = new ArrayList<>();
    protected boolean fail = false;

    public Landmarker(Hashtable<String, Integer> state, Hashtable<String, Action> Actions, ArrayList<String> goal) {
        _State = state;
        _Actions = Actions;
        _Goal = goal;
        //_Invariants = invariants;
        Integer num_MAX_iter = 0;
        initActionList();
        //cleanProblem();
        Enumeration<String> enumerator_states = state.keys();
        StepLandmark stepInit = new StepLandmark();
        stepInit.father = null;
        stepInit.step = 0;
        while(enumerator_states.hasMoreElements()){
            String predicate = enumerator_states.nextElement().toString();
            NodeLandmark no = new NodeLandmark(predicate);
            no.level = stepInit.step;
            stepInit.addNode(no);
        }
        _Steps.add(stepInit);
        StepLandmark lastStep = _Steps.get(_Steps.size()-1);
        while(!isGoal(lastStep) && num_MAX_iter < _Actions.size()){
            //Expandimos o último nó
            expand(lastStep);
            num_MAX_iter++;
            lastStep = _Steps.get(_Steps.size()-1);
        }
        if(num_MAX_iter == _Actions.size()){
            System.out.println("FAIL: no landmarks found.");
            fail = true;
        }else{
            //backtrackPlan();
            //printGoals();
            extract_landmarks();
			/*
			System.out.println("=========================================");
			System.out.println("Plano parcialmente ordenado (incluindo no-ops): ");
			System.out.println(_Plan.toString());
			System.out.println("=========================================");
			System.out.println("Plano parcialmente ordenado (sem no-ops): ");
			plotPlan();*/
        }
    }

    public void extract_landmarks(){
        //ArrayList<String> landmarks = new ArrayList<String>();
        ArrayList<String> SetGoals = new ArrayList<String>();
		/*Init subgoals*/
        ArrayList<String> _subgoal = new ArrayList<String>(_Goal);
        ArrayList<String> A = new ArrayList<String>();
        ArrayList<String> I = new ArrayList<String>();
        ArrayList<String> U = new ArrayList<String>();
        ArrayList<ArrayList<String>> list_preconditions = new ArrayList<ArrayList<String>>();
        for(int i = _Steps.size()-1;i>=0;i-=2){
            StepLandmark currentStep = _Steps.get(i);
			/*Get A: Let A be the set of actions from earlier levels of the RPG that add g*/
            I.clear();
            for(int j = 0;j< _subgoal.size();j++){
                String p = _subgoal.get(j);
                NodeLandmark n = currentStep.getNode(p);
                if(n.hasParent()){
                    for(NodeLandmark parent_node : n.getParent()){
                        if(parent_node.level < currentStep.step){
                            A.add(parent_node.predicate);
                        }
                    }
                }
            }
			/*Let A be the set of actions from earlier levels of the RPG that add g*/
            _subgoal.clear();
            for(String action_name : A){
				/*Let I be the intersection of the preconditions of all the actions in A*/
                Action action = _Actions.get(action_name);
                list_preconditions.add(filterList(action));
            }
            I = intersect(list_preconditions);
			/*for each i in I*/
            for(String pred : I){
				/*Add i to landmarks*/
                landmarks.add(pred);
				/*Add i to the earliest level that its achieved in the RPG to Goals*/
                _subgoal.add(pred);
            }
            _subgoal = removeDuplicate(_subgoal);
            A.clear();
			/*Let U be the union of the preconditions of the actions in A (except those in I)*/
            U = minusSet(list_preconditions, I);
            list_preconditions.clear();
			/*The literals in U are grouped by type and added to SetGoals*/
            SetGoals.addAll(U);
			/*For each s in SetGoals*/
            for(int k = 0;k< SetGoals.size();k++){
                String p = SetGoals.get(k);
                NodeLandmark n = currentStep.getNode(p);
                if(n.hasParent()){
					/*Let A be the set of actions from earlier levels of the RPG that add s*/
                    for(NodeLandmark parent_node : n.getParent()){
                        if(parent_node.level < currentStep.step){
                            A.add(parent_node.predicate);
                        }
                    }
                }
            }
			/*Let A be the set of actions from earlier levels of the RPG that add s*/
            SetGoals.clear();
            for(String action_name : A){
				/*Let I be the intersection of the preconditions of all the actions in A*/
                Action action = _Actions.get(action_name);
                list_preconditions.add(filterList(action));
            }
			/*for each i in I*/
            for(String pred : I){
				/*Add i to landmarks*/
                landmarks.add(pred);
				/*Add i to the earliest level that its achieved in the RPG to Goals*/
                _subgoal.add(pred);
            }
            _subgoal = removeDuplicate(_subgoal);
            A.clear();
        }
        landmarks = removeDuplicate(landmarks);
        System.out.println("Possible action landmarks: " + landmarks.toString());
    }

    public ArrayList<String> getLandmarks(){
        return landmarks;
    }

    private ArrayList<String> minusSet(ArrayList<ArrayList<String>> list, ArrayList<String> iList){
        ArrayList<String> returnList = new ArrayList<String>();
        if(list.size()>0){
            for(ArrayList<String> subList : list){
                returnList.addAll(subList);
                returnList = removeDuplicate(returnList);
            }
        }
        returnList.removeAll(iList);
        return returnList;
    }

    private ArrayList<String> intersect(ArrayList<ArrayList<String>> list){
        if(list.size()>0){
            ArrayList<String> instersect_list = new ArrayList<String>(list.get(0));
            for(ArrayList<String> iList : list){
                instersect_list.retainAll(iList);
            }
            return instersect_list;
        }
        return new ArrayList<String>();
    }

    private ArrayList<String> filterList(Action action){
        ArrayList<String> filteredList = new ArrayList<String>();
        for(String predicate : action._precond){
            if(!predicate.startsWith("~")){
                filteredList.add(predicate);
            }
        }
        return filteredList;
    }

    private ArrayList<String> removeDuplicate(ArrayList<String> U){
        Set<String> notDuplicate = new HashSet<String>(U);
        U.clear();
        U.addAll(notDuplicate);
        return U;
    }

    private void backtrackPlan() {
        Hashtable<String, Integer> achieved_preconds = new Hashtable<String, Integer>();
        StepLandmark currentStep = _Steps.get(_Steps.size()-1);
        ArrayList<String> _subgoal = new ArrayList<String>(_Goal);
        while(currentStep.father != null){
            ArrayList<String> _actualList = new ArrayList<String>();
            ArrayList<String> _actions_Partial_ordered = new ArrayList<String>();
            for(String p : _subgoal){
                NodeLandmark n = currentStep.getNode(p);
                currentStep.levelGoals.add(p);
                if(!achieved_preconds.containsKey(n.predicate)){
                    if(n.hasParent()){
                        for(NodeLandmark parent_node : n.getParent()){
                            String new_Param = parent_node.predicate;
                            _actualList.add(new_Param);
                            if(!new_Param.startsWith("No-op")){
                                _actions_Partial_ordered.add(new_Param);
                                achieved_preconds.put(n.predicate, 1);
                            }
							/*if(!achieved_preconds.containsKey(new_Param)){
								_actualList.add(new_Param);
								achieved_preconds.put(new_Param, 1);
							}
							if(!new_Param.startsWith("No-op")){
								_actions_Partial_ordered.add(new_Param);
							}*/
                        }
                    }
                }
            }
            _subgoal.clear();
            _subgoal.addAll(_actualList);
            if((currentStep.step %2)==0){
                _Plan.add(0, _actualList.toString());
                _ActionPlan.put(currentStep.step -1 , _actions_Partial_ordered);
            }
            if(currentStep.father != null){
                currentStep = currentStep.father;
            }
        }
    }

    private void printGoals(){
        StepLandmark currentStep = _Steps.get(_Steps.size()-1);
        System.out.println("=========================================");
        System.out.println("Goals by level: ");
        while(currentStep.father != null){
            System.out.println("Level " + currentStep.step + ": " + currentStep.levelGoals.toString());
            if(currentStep.father != null){
                currentStep = currentStep.father;
            }
        }
    }

    public Integer heuristicValue(){
        int hValue = 0;
        Enumeration e = _ActionPlan.keys();
        while(e.hasMoreElements()){
            Integer Key_Plan = Integer.parseInt(e.nextElement().toString());
            ArrayList<String> partialActions = _ActionPlan.get(Key_Plan);
            hValue += partialActions.size();
        }
        return hValue;
    }

    private void plotPlan(){
        Enumeration e = _ActionPlan.keys();
        while(e.hasMoreElements()){
            Integer Key_Plan = Integer.parseInt(e.nextElement().toString());
            ArrayList<String> partialActions = _ActionPlan.get(Key_Plan);
            System.out.println(partialActions.toString());
        }
    }

    public void initActionList(){
        Enumeration enumerator_actions = _Actions.keys();
        while(enumerator_actions.hasMoreElements()){
            String aName = enumerator_actions.nextElement().toString();
            //System.out.println(aName);
            _Actions_list.add(aName);
        }
    }

    public boolean isGoal(StepLandmark predicates){
        for(String pred : _Goal){
            if(!predicates.Contains(pred)){
                return false;
            }
        }
        return true;
    }

    private void expand(StepLandmark predicates_list){
        StepLandmark ActionStep = new StepLandmark();
        StepLandmark PredicateStep = new StepLandmark();
        PredicateStep.step = predicates_list.step + 2;
        ActionStep.step = predicates_list.step + 1;
        //1 copy predicates (no-op predicates)
        for(NodeLandmark predicate_node : predicates_list.getIterator()){
            PredicateStep.addNode(predicate_node);
        }
        //2 expand actions if possible (applicable)
        for(String action_name : _Actions_list) {
            Action a = _Actions.get(action_name);
            if(isActionApplicable(a, predicates_list)){
                NodeLandmark no = new NodeLandmark(action_name);
                if(no.level > ActionStep.step) {
                    no.level = ActionStep.step;
                }
                ActionStep.addNode(no);
                for(String precondition : a._precond) {
                    if(!precondition.startsWith("~")){
                        ActionStep.updateParentNode(action_name, predicates_list.getNode(precondition));
                    }
                }
                if(a.IsObservation || a._IsNondeterministic){
                    for(Branch b : a._Branches){
                        for(String s : b._Branches){
                            if (!s.startsWith("~")) {
                                addEffect(PredicateStep, s, no);
                            }
                        }
                    }
                }else {
                    for (Effect e : a._Effects) {
                        if (isEffectApplicable(e, predicates_list)) {
                            for (String eff : e._Effects) {
                                if (!eff.startsWith("~")) {
                                    addEffect(PredicateStep, eff, no);
                                }
                            }
                        }
                    }
                }
            }
        }
        ActionStep.father = predicates_list;
        PredicateStep.father = ActionStep;
        _Steps.add(ActionStep);
        _Steps.add(PredicateStep);
        last_layer = ActionStep.step;
    }

    private void addEffect(StepLandmark PredicateStep, String effect, NodeLandmark no){
        //Verify if the node already exists
        if(effect.startsWith("~")){
            return;
        }
        if(PredicateStep.Contains(effect)){
            PredicateStep.updateParentNode(effect, no);
        }else{
            NodeLandmark node_effect = new NodeLandmark(effect);
            if(node_effect.level > PredicateStep.step){
                node_effect.level = PredicateStep.step;
                if(!_GoalsAchieved.containsKey(node_effect.predicate)){
                    _GoalsAchieved.put(node_effect.predicate, PredicateStep.step);
                }
                PredicateStep.addNode(node_effect);
                //ActionStep.updateSuccessorNode(action_name, node_effect);
                PredicateStep.updateParentNode(effect, no);
            }
        }
    }

    /**Verify if the effect is applicable*/
    private boolean isEffectApplicable(Effect e, StepLandmark s) {
        for(String cond : e._Condition){
            if(cond.startsWith("~")){
                continue;
            }
            if(!s.Contains(cond)){
                return false;
            }
        }
        return true;
    }

    public void expandStep(StepLandmark predicates_list) {
        // 1 expand actions if possible (applicable)
        StepLandmark ActionStep = new StepLandmark();
        StepLandmark PredicateStep = new StepLandmark();
        PredicateStep.step = predicates_list.step + 2;
        ActionStep.step = predicates_list.step + 1;
        for(String action_name : _Actions_list) {
            Action a = _Actions.get(action_name);
            if(isActionApplicable(a, predicates_list)){
                NodeLandmark no = new NodeLandmark(action_name);
                if(no.level > ActionStep.step) {
                    no.level = ActionStep.step;
                }
                ActionStep.actionsHash.put(action_name, 1);
                ActionStep.addNode(no);
                for(String precondition : a._precond) {
                    predicates_list.updateSuccessorNode(precondition, no);
                    ActionStep.updateParentNode(action_name, predicates_list.getNode(precondition));
                }
				/*for(String effect : a._Positive_effects){
					NodeLandmark node_effect = new NodeLandmark(effect);
					if(node_effect.level > PredicateStep.step){
						node_effect.level = PredicateStep.step;
					}
					PredicateStep.addNode(node_effect);
					ActionStep.updateSuccessorNode(action_name, node_effect);
					PredicateStep.updateParentNode(effect, no);
				}*/
            }
        }
        // 2 Add no-ops actions and effects
        for(NodeLandmark predicate : predicates_list.getIterator()){
            if(!PredicateStep.Contains(predicate.predicate)){
                NodeLandmark no = new NodeLandmark("No-op-" + predicate.toString());
                NodeLandmark node_effect_no = new NodeLandmark(predicate.toString());
                node_effect_no.level = predicate.level;
                ActionStep.addNode(no);
                ActionStep.updateParentNode(no.toString(), predicate);
                PredicateStep.addNode(node_effect_no);
                ActionStep.updateSuccessorNode(no.predicate, node_effect_no);
                PredicateStep.updateParentNode(node_effect_no.predicate, no);
            }
        }
        ActionStep.father = predicates_list;
        PredicateStep.father = ActionStep;
        _Steps.add(ActionStep);
        _Steps.add(PredicateStep);
        last_layer = ActionStep.step;
    }

    /**Verify if the action is applicable*/
    private boolean isActionApplicable(Action a, StepLandmark s){
        for(String precondition : a._precond){
            if(precondition.startsWith("~")){
                continue;
            }
            if(!s.Contains(precondition)){
                return false;
            }
			/*if(isInvariant(precondition)){
				continue;
			}
			if(!precondition.contains("^")){
				if(!s.Contains(precondition)){
					return false;
				}
			}else{
				boolean flag = false;
				String[] orPrecond = precondition.split("\\^");
				for(String orP : orPrecond){
					if(s.Contains(orP)){
						flag = true;
						break;
					}
				}
				if(!flag){
					return false;
				}
			}*/
        }
        return true;
    }
}
