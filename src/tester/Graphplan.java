package tester;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Set;
import java.util.Stack;

import pddlElements.*;
/**
 * 
 * @author ignasi
 *
 */

public class Graphplan {
	
	private ArrayList<String> _Actions_list = new ArrayList<String>();
	private Hashtable<String, Action> _Actions = new Hashtable<String, Action>();
	private HashSet<String> _State = new HashSet<String>();
	private ArrayList<String> _Goal = new ArrayList<String>();
	protected ArrayList<String> _Plan = new ArrayList<String>();
	protected Integer last_layer = 0;
	protected boolean fail = false;
	public int heuristicValue = 100000000;
	private StepLandmark layerMembershipActions = new StepLandmark();
	private StepLandmark layerMembershipFacts = new StepLandmark();

	public Graphplan(HashSet<String> state, Hashtable<String, Action> Actions, ArrayList<String> goal) {
		_State = state;
		_Actions = Actions;
		_Goal = goal;
		//_Invariants = invariants;
		initActionList();
		expand();
		if(last_layer == _Actions_list.size()){
			heuristicValue = Integer.MAX_VALUE;
		}else{
			extract();
		}
		
		if(_Plan.isEmpty() && !isGoal(layerMembershipFacts)){
			heuristicValue = Integer.MAX_VALUE;
		}else{
			heuristicValue = _Plan.size();
		}		
		//cleanProblem();
		//heuristicValue = heuristicGraphPlan();
		//System.out.println(_Plan.toString());
		//System.out.println("Hvalue: " + heuristicValue + " size relaxed plan: " + _Plan.size());
	}
	
	private void extract(){
		ArrayList<HashSet<String>> gI = initGoalLayer();
		HashSet<String> solved = new HashSet<String>();
		//Init with goal predicates:
		for(String p : _Goal){
			NodeLandmark n = layerMembershipFacts.getNode(p);
			gI.get(n.level).add(p);
		}
		//For each level in decreasing order:
		for(int i=last_layer;i>0;i--){
			if(gI.get(i).isEmpty()){
				continue;
			}
			HashSet<String> currentGoalSet = gI.get(i);
			Iterator<String> iterator = currentGoalSet.iterator();
			while (iterator.hasNext()){				
				String p = iterator.next().toString();
				if(solved.contains(p)){
					continue;
				}
				solved.add(p);
				NodeLandmark n = layerMembershipFacts.getNode(p);
				NodeLandmark selectedAction = chooseAction(n.getParent());
				_Plan.add(selectedAction.predicate);
				for(NodeLandmark precondition : selectedAction.getParent()){
					gI.get(precondition.level).add(precondition.predicate);
				}
			}
		}
	}
	
	private NodeLandmark chooseAction(ArrayList<NodeLandmark> ActionList){
		int best = Integer.MAX_VALUE;
		NodeLandmark bestAction = new NodeLandmark("");
		Hashtable<String, Integer> actionsCosts = new Hashtable<String, Integer>();
		for(NodeLandmark n : ActionList){
			int cost = 0;
			for(NodeLandmark precondition : n.getParent()){
				if(layerMembershipFacts.Contains(precondition.predicate)){
					cost = cost + precondition.level;
				}
			}
			actionsCosts.put(n.predicate, cost);
			if(cost<best){
				best = cost;
				bestAction = n;				
			}
		}
		return bestAction;
	}
	
	private ArrayList<HashSet<String>> initGoalLayer(){
		ArrayList<HashSet<String>> returnList = new ArrayList<HashSet<String>>();
		for(int iter = 0; iter<=last_layer;iter++){
			HashSet<String> setPredicates = new HashSet<String>();
			returnList.add(iter, setPredicates);
		}
		return returnList;
	}

	public void initActionList(){
		Enumeration<String> enumerator_actions = _Actions.keys();
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
	
	private void expand(){
		//Init state
		Enumeration<String> e = Collections.enumeration(_State);
	    while(e.hasMoreElements()){
	    	String p = e.nextElement().toString();
	    	NodeLandmark node = new NodeLandmark(p);
	    	node.level = 0;
	    	layerMembershipFacts.addNode(node);
	    }
	    last_layer = 0;
		while(!containsGoal(layerMembershipFacts) && last_layer < _Actions_list.size()){
			//ArrayList<String> _actions = new ArrayList<>();
			for(String action_name : _Actions_list){
				Action a = _Actions.get(action_name);
				if(isApplicable(a._precond, layerMembershipFacts, last_layer)){
					//_actions.add(action_name);
					NodeLandmark actionNode = new NodeLandmark(action_name);
					actionNode.level = last_layer;
					addPreconditions(a, actionNode, last_layer);
					layerMembershipActions.addNode(actionNode);
					for(Effect effect: a._Effects){
		    			if(effect._Condition.isEmpty() || isApplicable(effect._Condition, layerMembershipFacts, last_layer)){
		    				applyEffects(effect._Effects, actionNode, last_layer);		    				
		    			}
		    		}
				}
			}
			last_layer++;
		}
	}

	private void addPreconditions(Action a, NodeLandmark actionNode, int i) {
		for(String precondition : a._precond){
			if(precondition.startsWith("~")){
				continue;
			}
			NodeLandmark n = layerMembershipFacts.getNode(precondition);
			actionNode.addPredecessor(n);
		}
	}

	private void applyEffects(ArrayList<String> _Effects, NodeLandmark n, int i) {
		for(String eff: _Effects){
			if(eff.startsWith("~")){
				//We dont remove negative effects!
			}else{
				if(!layerMembershipFacts.Contains(eff)){
					NodeLandmark nodePredicate = new NodeLandmark(eff);
					nodePredicate.level = i+1;
					nodePredicate.addPredecessor(n);
	            	layerMembershipFacts.addNode(nodePredicate);
	            }
			}            
		}
	}

	private boolean containsGoal(StepLandmark layerMembershipFacts2) {
		for(String pred : _Goal){
			if(!layerMembershipFacts2.Contains(pred)){
				return false;
			}
		}
		return true;
	}

	public ArrayList<String> getPlan(){
		return _Plan;
	}
	
	/**Verify if a set of conditions are met*/
	private boolean isApplicable(ArrayList<String> conditions, StepLandmark s, int i){
		for(String precondition : conditions){
			/*Cases:
			 * 1: precondition positive: if ~precondition inside s return false
			 * 2: precondition negative: if precondition inside s return false
			*/
			if(!precondition.startsWith("~")){
				if(!s.Contains(precondition) || s.getNode(precondition).level >= i){
					return false;
				}
			}else {
				if(s.Contains(precondition.substring(1)) && s.getNode(precondition.substring(1)).level <= i){
					return false;
				}
			}
		}
		return true;
	}
}
