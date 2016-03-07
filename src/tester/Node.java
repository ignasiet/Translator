package tester;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.PriorityQueue;
import java.util.Queue;

import pddlElements.Action;
import pddlElements.Branch;
import pddlElements.Effect;

public class Node {

	public HashSet<String> _State = new HashSet<String>();
	public String _BestAction;
	private int nMax = 200;
	public int heuristicValue = Integer.MAX_VALUE;
	public ArrayList<Node> _NextStates = new ArrayList<Node>();
	public boolean solved = false;
	public boolean terminal = false;
	public Queue<Node> _SuccessorStates = initFringe();
	public int ValueState;
	public ArrayList<Action> applicableActions;
	public int terminalCost = Integer.MAX_VALUE;
	public Hashtable<String, Integer> Qv = new Hashtable<String, Integer>();
	public Node parent;
	public Action _LastAction;
	public Integer pathCost = 0;
	public Integer fCost;
	private Node unsolvedChild;
	public String _BestHeuristicAction;
	
	
	public boolean canApply(Action a) {
		for(String precondition : a._precond){
			if(precondition.startsWith("~")){
				if(contains(precondition.substring(1))){
					return false;
				}
			}else{
				if(!contains(precondition)){
					return false;
				}
			}
		}
		return true;
	}
	
	public boolean canApplyConditions(ArrayList<String> cond){
		for(String precondition : cond){
			if(precondition.startsWith("~")){
				if(contains(precondition.substring(1))){
					return false;
				}
			}else{
				if(!contains(precondition)){
					return false;
				}
			}
		}
		return true;
	}
	
	private Queue<Node> initFringe() {
		PriorityQueue<Node> fringe = new PriorityQueue<Node>(nMax, 
				new Comparator<Node>(){
			public int compare(Node lhs, Node rhs) {
				return (int) (lhs.fCost - rhs.fCost);
			}
		});
		return fringe;
	}

	public boolean contains(String pred){
		if(_State.contains(pred)){
			return true;
		}else{
			return false;
		}
	}

	/**Verify if the conditional effect is applied*/
	public boolean isEffectApplicable(Effect e){
		if(e._Condition.isEmpty()){
			return true;
		}else{
			for(String precondition : e._Condition){
				if(!precondition.startsWith("~")){
					if(!_State.contains(precondition)){
						//System.out.println(a.Name);
						return false;
					}
				}else {
					if(_State.contains(precondition.substring(1))){
						return false;
					}
				}
			}
			return true;
		}
	}
	
	public void setParent(Node parent) {
		this.parent = parent;
	}

	public void setLastAction(Action a) {
		_LastAction = a;		
	}
	
	public ArrayList<Node> getChildrenAction(String action){
		ArrayList<Node> returnList = new ArrayList<Node>();
		for(Node s : _NextStates){
			if(s._LastAction.Name.equals(action)){
				returnList.add(s);
			}
		}
		return returnList;
	}
	
	public boolean checkChildrenSolved(String action){
		boolean solvedChildren = true;
		for(Node s : _NextStates){
			if(s._LastAction.Name.equals(action)){
				if(!s.solved){
					solvedChildren = false;
					unsolvedChild = s;
				}
			}
		}
		return solvedChildren;
	}
	
	public Node unsolvedChild(){
		return unsolvedChild;
	}

	public Node applyBranch(Branch b) {
		Node sucessorNode = new Node();
		sucessorNode._State =  (HashSet<String>) _State.clone();
		for(String effectC : b._Branches){
			if(effectC.startsWith("~")){
				sucessorNode._State.remove(effectC.substring(1));
			}else{
				sucessorNode._State.add(effectC);
			}
		}
		return sucessorNode;
	}
	
	public Integer argMin(){
		Integer r = Integer.MAX_VALUE;
		for(Action a : applicableActions){
			if(Qv.get(a.Name) < r){
				r = Qv.get(a.Name);
			}
		}
		return r;
	}

	public Node pickNextBestState() {
		Node s = _SuccessorStates.poll();
		if(s == null){
			terminal = true;
			return null;
		}else{
			_BestAction = s._LastAction.Name;
		}		
		return s;
	}
}
