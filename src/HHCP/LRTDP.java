package HHCP;

import java.util.*;

/**
 * Created by ignasi on 11/09/17.
 */
public class LRTDP {

    private HashSet<BitSet> solved = new HashSet<BitSet>();
    private Problem problem;
    private Heuristic h;
    private ArrayList<Integer> landmarks;
    private PriorityQueue<Node> fringe;
    private HashMap<BitSet, ArrayList<Node>> nextStates = new HashMap<BitSet, ArrayList<Node>>();
    private HashMap<BitSet, Integer> values = new HashMap<BitSet, Integer>();

    public LRTDP(Problem p, Problem heuristicP, ArrayList<String> l, JustificationGraph jG, String heuristic) {
        problem = p;
        initHeuristic(heuristicP, l, jG, heuristic);
        while(!solved.contains(p.getInitState())){
            trial(p.getInitState());
        }
    }

    //TODO: dead-ends and cycles, what to do?
    private void trial(BitSet initState) {
        Stack<Node> visited = new Stack<Node>();
        BitSet s = (BitSet) initState.clone();
        Comparator<Node> comparator = new NodeComparator();
        fringe = new PriorityQueue<Node>(100, comparator);
        Node initialNode = searchHelper.initLayers(s, problem);
        while(!initialNode.holds(problem.getGoal())){
        	fringe.clear();
            if(visited.contains(initialNode.getState())) continue;
            //Insert into visited
            visited.push(initialNode);
            //Check termination at goal states
            if(searchHelper.entails(s, problem.getGoal())) break;
            //Pick best action and update hash
            expandState(initialNode);
            initialNode.greedyAction = greedyAction(initialNode);
            update(initialNode);
            //Obtain the best (heuristic) successor
            Node greedySuccessor = pickNextState(initialNode);
            initialNode = searchHelper.initLayers(greedySuccessor.getState(), problem);
        }
        solved.add((BitSet) initialNode.getState().clone());
        values.put((BitSet) initialNode.getState().clone(), 0);
        System.out.println("End a trial");
        while(!visited.isEmpty()){
            Node n = visited.pop();
            if(!checkSolved(n)) break;
        }
    }

    private boolean checkSolved(Node n) {
        boolean rv = true;
        Stack<Node> open = new Stack<Node>();
        Stack<Node> closed = new Stack<Node>();
        if(!solved.contains(n.getState())){
            open.push(n);
        }
        while(!open.isEmpty()){
            Node s = open.pop();
            closed.push(s);
            //Check residual
            if(residual(s) > 0){
            	rv = false;
            	continue;
            }
            //Expand state
            ArrayList<Node> succs = s.successors.get(s.greedyAction);
        	for(Node succ : succs){
        		//TODO: verify if contains is better than search
        		if(!solved.contains(succ.getState()) && (!open.contains(succ) || !closed.contains(succ))){
        			open.push(succ);
        		}
        	}
        }
        if(rv){
            //label relevant states
            while(!closed.isEmpty()){
                Node s_prima = closed.pop();
                solved.add((BitSet) s_prima.getState().clone());
            }
        }else{
            //update states with residuals and ancestors
            while(!closed.isEmpty()){
                Node s_prima = closed.pop();

            }
        }
        return false;
    }
    
    private int residual(Node n){
    	//Take the minimal action
    	int greedyValue = Integer.MAX_VALUE;
    	int residual = 0;
    	for(int action : n.successors.keySet()){
    		int succValue = Integer.MAX_VALUE;
    		for(Node successor : n.successors.get(action)){    			
    			if(successor.value >= Integer.MAX_VALUE){
    				succValue = successor.getH();
    			}else{
    				succValue = successor.value;
    			}
    		}
    		//Verify that it is still the same action
    		if((succValue + problem.cost[action]) < values.get(n.getState())){
    			residual = Math.abs((succValue + problem.cost[action]) - values.get(n.getState()));
				n.greedyAction = action;
				n.value = succValue + problem.cost[action];
				values.put(n.getState(), n.value);
			}
    	}
    	return residual;    	
    }

    private void initHeuristic(Problem heuristicP, ArrayList<String> l, JustificationGraph jG, String heuristic) {
        if(!l.isEmpty()){
            landmarks = new ArrayList<>();
        }
        h = new Heuristic(heuristicP, landmarks, jG, heuristic);
        h.useCosts(heuristicP.cost);
    }

    private int greedyAction(Node n) {        
        if(!fringe.isEmpty()) {
            return fringe.poll().indexAction;
        }
        return -1;
    }
    
    private void expandState(Node n){
    	for(int action = n.getScheduledActions().nextSetBit(0); action >= 0; action = n.getScheduledActions().nextSetBit(action+1)){
            VAction vAct = problem.getAction(action);
            ArrayList<Node> listSucc = new ArrayList<Node>();
            if(vAct.isNondeterministic || vAct.isObservation){
                ArrayList<Node> successors = n.applyNonDeterministicAction(vAct,problem);
                for(Node succ : successors){
                    searchHelper.updateHeuristic(succ, n, vAct, h);
                    listSucc.add(succ);
                    fringe.add(succ);
                }
            }else{
                Node child = n.applyDeterministicAction(vAct, problem);
                searchHelper.updateHeuristic(child, n, vAct, h);
                listSucc.add(child);
                fringe.add(child);
            }
            n.successors.put(action, listSucc);
        }
    }

    private void update(Node n){
    	n.value = problem.cost[n.greedyAction];
    	ArrayList<Node> succs = n.successors.get(n.greedyAction);
    	for(Node succ : succs){
    		n.value += succ.getH();
    	}
    	values.put(n.getState(), n.value);
    }

    public Node pickNextState(Node n){
        Random r = new Random();
        ArrayList<Node> succs = n.successors.get(n.greedyAction);
        //nextStates.put((BitSet) n.getState().clone(), new ArrayList<Node>(succs));
        return succs.get(r.nextInt(succs.size()));
    }


}
