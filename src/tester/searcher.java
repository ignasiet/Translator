package tester;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import pddlElements.Action;
import pddlElements.Branch;
import pddlElements.Domain;
import pddlElements.Effect;
public class searcher {
	private Domain _Domain;
	
	public void searchPlan(Domain domain){
		_Domain = domain;
		Node initialState = getInitialState(domain.state);
		
		debuggerTester(initialState);
	}
	
	private boolean goalTest(Node node){
		for(String predicate : _Domain.goalState){
			if(!node.contains(predicate)){
				return false;
			}
		}
		return true;
	}
	
	private Node applyAction(Action a, Node s) {
		Node node_sucessor = new Node();
		node_sucessor.setLastAction(a);
		node_sucessor._State = (HashSet<String>) s._State.clone();
		//1-Apply conditional effects:
		if(!a.IsObservation){
			for(Effect conditionalEffect : a._Effects){
				if(s.isEffectApplicable(conditionalEffect)){
					for(String effectC : conditionalEffect._Effects){
						if(effectC.startsWith("~")){
							System.out.println("Removing: " + effectC.substring(1));
							node_sucessor._State.remove(effectC.substring(1));
						}else{
							System.out.println("Adding: " + effectC);
							node_sucessor._State.add(effectC);
						}
					}
				}
			}
		}else{
			System.out.println("Choose branch: ");
			int i = 0;
			for(Branch b : a._Branches){
				System.out.println(i +": " + b._Branches.toString());
				i++;
			}
			BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(System.in));
	        String input;
			try {
				input = bufferedReader.readLine();
				int number = Integer.parseInt(input);
				for(String b : a._Branches.get(number)._Branches){
					if(b.startsWith("~")){
						//System.out.println("Removing: " + b.substring(1));
						node_sucessor._State.remove(b.substring(1));
					}else{
						//System.out.println("Adding: " + b);
						node_sucessor._State.add(b);
					}
				}
				//node = list_states.get(number);
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}		
		return node_sucessor;
	}
	
	private void Heuristic(Node child, Node father){
		Graphplan gp = new Graphplan(child._State, _Domain.list_actions, _Domain.goalState);
		child.heuristicValue = gp.heuristicValue;
		if(gp.heuristicValue == 0){
			child.solved = true;
		}
		child.pathCost = father.pathCost + 1;
		child.fCost = child.heuristicValue + child.pathCost;
		if(!gp.getPlan().isEmpty()){
			child._BestHeuristicAction = gp.getPlan().get(gp.getPlan().size()-1);
		}
		child.setParent(father);			
		father._NextStates.add(child);
	}
	
	public void debuggerTester(Node node){
		while(!goalTest(node)){
			System.out.println("Choose action (wisely!): ");
			matchApplicableActions(node);
			ArrayList<Action> applicable_action_list = node.applicableActions;
			ArrayList<Node> list_states = new ArrayList<Node>();
			int i = 0;
			for(Action a : applicable_action_list){				
				System.out.println(i + " Action: " + a.Name);
				// " Heuristic: " + child.heuristicValue + " Fvalue: " + child.fCost
				i++;
			}
			BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(System.in));
	        String input;
			try {
				input = bufferedReader.readLine();
				int number = Integer.parseInt(input);
				node = applyAction(applicable_action_list.get(number), node);
				//Heuristic(child, node);
				//list_states.add(i, child);
				//node = list_states.get(number);
				System.out.println(node._State.toString());
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}	        
		}
	}
	
	private Node getInitialState(Hashtable<String, Integer> state) {
		Node s = new Node();
		Enumeration<String> e = state.keys();
		while(e.hasMoreElements()){
			s._State.add(e.nextElement().toString());
		}
		Graphplan gp = new Graphplan(s._State, _Domain.list_actions, _Domain.goalState);
		s.heuristicValue = gp.heuristicValue;
		if(!gp.getPlan().isEmpty()){
			s._BestHeuristicAction = gp.getPlan().get(gp.getPlan().size()-1);
		}
		return s;
	}
	
	private void matchApplicableActions(Node s){
		ArrayList<Action> return_list = new ArrayList<Action>();
		if(s._BestHeuristicAction != null){
			return_list.add(_Domain.list_actions.get(s._BestHeuristicAction));
		}else{
			Enumeration<String> e = _Domain.list_actions.keys();
			while(e.hasMoreElements()){
				Action a = _Domain.list_actions.get(e.nextElement().toString());
				if(s.canApply(a)){
					return_list.add(a);
				}
			}
		}
		if(return_list.size() == 0){
			s.terminal = true;
		}else{
			s.applicableActions = return_list;
		}
	}
}
