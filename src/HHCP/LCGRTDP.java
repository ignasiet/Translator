package HHCP;

import java.math.BigInteger;
import java.util.*;

/**
 * Created by ignasi on 11/09/17.
 */
public class LCGRTDP {

    private HashSet<BitSet> solved = new HashSet<BitSet>();
    private Problem problem;
    private Heuristic h;
    private HashSet<BitSet> visited;
    private HashSet<BitSet> deadEnds = new HashSet<BitSet>();
    private ArrayList<Integer> landmarks;
    private PriorityQueue<Node> fringe;
    private HashMap<BitSet, Integer> forbiddenActionPairs = new HashMap<BitSet, Integer>();
    private HashMap<BitSet, ArrayList<Node>> nextStates = new HashMap<BitSet, ArrayList<Node>>();
    private HashMap<BitSet, Long> values = new HashMap<BitSet, Long>();
    private PartialPolicy policyP = new PartialPolicy();
    //private HashMap<BitSet, Integer> GreedyEnvelope = new HashMap<BitSet, Integer>();
    private long dValue = 400000000000l;
    private HashMap<BitSet, Integer> numberDE = new HashMap<>();

    public LCGRTDP(Problem p, Problem heuristicP, ArrayList<String> l, JustificationGraph jG, String heuristic, long cost) {
        problem = p;
        dValue = cost;
        initHeuristic(heuristicP, l, jG, heuristic);
        double startTime = System.currentTimeMillis();
        while(!solved.contains(p.getInitState())){
            //trial(p.getInitState());
            genWeakSolution(p.getInitState());
            //driver(p.getInitState());
        }
        double endTime = System.currentTimeMillis();
        System.out.println("Expected cost of the solution: " + values.get(p.getInitState()));
        searchHelper.printStats(policyP, startTime, endTime, p);
        searchHelper.printPolicy(p.getInitState(), policyP, p);
    }

    private void genWeakSolution(BitSet initState) {
        BitSet s = (BitSet) initState.clone();
        Comparator<Node> comparator = new NodeComparator();
        fringe = new PriorityQueue<Node>(100, comparator);
        //HashSet<BitSet> visited = new HashSet<BitSet>();
        visited = new HashSet<BitSet>();
        Node initialNode = searchHelper.initLayers(new Node(s), problem);
        fringe.add(initialNode);
        while(!initialNode.holds(problem.getGoal()) && !solved(initialNode.getState())) {
            if (fringe.isEmpty()) {
                System.out.println("No weak plan found.\nThe initial State for this search may have caused a Dead-end.");
                update(initialNode);
                break;
            }
            /*if(initialNode.getCost() > bestSolution){
                System.out.println("CUTOFF!");
                break;
            }*/
            Node node = searchHelper.initLayers(fringe.poll(), problem);
            //Node node = searchHelper.initLayers(pickNextState(n)), problem)-
            //if(node.parent != null) node.parent.greedyAction = node.indexAction;
            if (visited.contains(node.getState())){
                continue;
            }
            visited.add(node.getState());
            if (node.holds(problem.getGoal()) || solved(node.getState()) ) {
                System.out.println("Solution found");
                regressPlan(node);
                break;
            }
            expand(node);
            if(node.successors.isEmpty()){
                //node.value = Math.min();
                update(node);
                continue;
            }
            update(node);
            //pickNextState(node);
            if(successorsSolved(node)){
                System.out.println("Leaf states found.");
                update(node);
                regressPlan(node);
                break;
            }
        }
    }

    private boolean successorsSolved(Node node) {
        /*TODO: must test all descendants or only the greedy action descendants?*/
        /*boolean sSolved = true;
        for(int action : node.successors.keySet()){
            for(Node successor : node.successors.get(action)){
                if(!solved(successor.getState())) return false;
            }
        }
        return sSolved;*/
        boolean sSolved = true;
        for(Node successor : node.successors.get(node.greedyAction)){
            if(!solved(successor.getState())) return false;
        }
        return sSolved;
    }

    private void regressPlan(Node node) {
        //boolean flag = true;
        if(node.holds(problem.getGoal())){
            node.value = 0;
            solved.add((BitSet) node.getState().clone());
            values.put((BitSet) node.getState().clone(), 0L);
        }else{
            node.greedyAction = greedyAction(node);
            if(checkSolved(node)) policyP.put((BitSet) node.getState().clone(), node.greedyAction);
        }
        while(node.parent != null){
            if(node.parent != null) node.parent.greedyAction = node.indexAction;
            node = node.parent;
            update(node);
            //if(!flag) continue;
            if(!checkSolved(node)){
            	//if dead-end found, update all the way back to the parent
            	/*if(deadEndSuccessors(node)){
            		while(node.parent != null){
            			updateWave(node);
            			node = node.parent;
            		}
            	}*/
                break;
            }else{
                policyP.put((BitSet) node.getState().clone(), node.greedyAction);
            }
        }
    }

    private boolean solved(BitSet state) {
        boolean b = solved.contains(state);
        return b;
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
                if(n.getState() != s.getState()){
                    System.out.println("Non-deterministic outcome not treated!");
                }
                rv = false;
                continue;
            }
            //Expand state:
            /*Problem encountered: state s has a residual of 0 calculated with the
             * greedy action, however has a child that is not solved.
             * Approach: get out of this function and keep searching a solution.*/
            ArrayList<Node> succs = s.successors.get(s.greedyAction);
            for(Node succ : succs){
                if(!solved(succ.getState()) && !open.contains(succ) && !closed.contains(succ)){
                    if(succ.holds(problem.getGoal())){
                        solved.add((BitSet) succ.getState().clone());
                        values.put((BitSet) succ.getState().clone(), 0L);
                    }else {
                        return false;
                        //open.push(succ);
                    }
                }
            }
        }
        if(rv){
            //label relevant states
            while(!closed.isEmpty()){
                Node sPrima = closed.pop();
                update(sPrima);
                solved.add((BitSet) sPrima.getState().clone());
                //updateWave(sPrima);
            }
        }else{
            //update states with residuals and ancestors
            while(!closed.isEmpty()){
                Node sPrima = closed.pop();
                update(sPrima);
            }
        }
        return rv;
    }
    
    private void updateWave(Node node){
    	if(deadEndSuccessors(node)) {
        	values.put((BitSet) node.getState().clone(), node.value);
        }else{
        	values.put((BitSet) node.getState().clone(), maxQValue(node));
        }
    }

    private Long maxQValue(Node node) {
        long max = 0;
        for(Node successor : node.successors.get(node.greedyAction)){
            if(max < successor.value){
                max = successor.value;
            }
        }
        return max;
    }

    private long minQValue(Node node) {
        long min = Long.MAX_VALUE;
        for(Node successor : node.successors.get(node.greedyAction)){
            if(min > successor.value){
                min = successor.value;
            }
        }
        return min;
    }

    private boolean zeroCostSuccessors(Node node) {
        boolean sSolved = true;
        for(Node successor : node.successors.get(node.greedyAction)){
            if(!solved(successor.getState()) || deadEnds.contains(successor.getState()) || successor.value > 0) return false;
        }
        return sSolved;
    }

    private boolean deadEndSuccessors(Node node) {
        boolean deadchild = false;
        for(Node successor : node.successors.get(node.greedyAction)){
            if(deadEnds.contains(successor.getState())) return true;
        }
        return deadchild;
    }

    private boolean notDeadEndSuccessors(Node node) {
        boolean sSolved = true;
        for(Node successor : node.successors.get(node.greedyAction)){
            if(!solved(successor.getState()) || deadEnds.contains(successor.getState())) return false;
        }
        return sSolved;
    }

    private long residual(Node n){
        //Take the minimal action
        long residual = 0L;
        int action = greedyAction(n);
        if(!n.successors.containsKey(action)) return 1;
        long succValue = qValue(n, action);
        if((succValue + problem.cost[action]) < values.get(n.getState())){
            residual = Math.abs((succValue + problem.cost[action]) - values.get(n.getState()));
        }
        return residual;
    }

    private long getValue(Node n){
        if(values.containsKey(n.getState())){
            return values.get(n.getState());
        }
        return Long.MAX_VALUE;
    }

    private void initHeuristic(Problem heuristicP, ArrayList<String> l, JustificationGraph jG, String heuristic) {
        if(!l.isEmpty()){
            landmarks = new ArrayList<>();
        }
        h = new Heuristic(heuristicP, landmarks, jG, heuristic);
        h.useCosts(heuristicP.cost);
    }

    private void expand(Node n){
        for(int action = n.getScheduledActions().nextSetBit(0); action >= 0; action = n.getScheduledActions().nextSetBit(action+1)){
            if(forbiddenActionPairs.containsKey(n.getState()) && (action == forbiddenActionPairs.get(n.getState()))){
                continue;
            }
            VAction vAct = problem.getAction(action);
            ArrayList<Node> listSucc = new ArrayList<Node>();
            if(vAct.isNondeterministic || vAct.isObservation){
                ArrayList<Node> successors = n.applyNonDeterministicAction(vAct,problem);
                for(Node succ : successors){
                    if(n.visited.contains(succ.getState())) {
                        continue;
                    }
                    updateCostExpandedChild(succ, n, vAct);
                    if(isDeadEnd(succ)){
                        processDeadEnds(succ, n, vAct);
                    }
                    listSucc.add(succ);
                    if(!solved(succ.getState())) fringe.add(succ);
                    succ.addVisited(n.visited);
                }
                /*for(Node succ : listSucc){
                    succ.setHeuristic(hAdd);
                    if(!solved(succ.getState())) fringe.add(succ);
                }*/
            }else{
                Node child = n.applyDeterministicAction(vAct, problem);
                if(n.visited.contains(child.getState())) {
                    continue;
                }
                if(n.parent != null && child.getState().equals(n.parent.getState())){
                    continue;
                }
                updateCostExpandedChild(child, n, vAct);
                //child.setHeuristic(Math.min(dValue, child.getH()));
                child.setHeuristic(Math.min(Long.MAX_VALUE, child.getH()));
                listSucc.add(child);
                if(!solved(child.getState())) fringe.add(child);
            }
            n.successors.put(action, listSucc);
        }
    }

    private void processDeadEnds(Node child, Node father, VAction vAct){
        deadEnds.add(child.getState());
        BitSet deadend = (BitSet) father.getState().clone();
        deadend.and(child.getState());
        deadEnds.add(deadend);
        numberDE.put(child.getState(), 1);
        //forbiddenActionPairs.put((BitSet) father.getState().clone(), vAct.index);
    }

    private boolean isDeadEnd(Node succ){
        if(deadEnds.contains(succ.getState()) || succ.getH() >= Long.MAX_VALUE){
            deadEnds.add(succ.getState());
            //succ.setHeuristic(Math.min(Long.MAX_VALUE, succ.getH()));
            //succ.setHeuristic(Math.min(dValue, succ.getH()));
            solved.add((BitSet) succ.getState().clone());
            values.put((BitSet) succ.getState().clone(), dValue);
            succ.setHeuristic(dValue);
            return true;
        }
        return false;
    }

    private void setParent(Node child, Node ancestor, VAction action) {
        child.parent = ancestor;
        child.parentAction = action.getName();
        child.indexAction = action.index;
    }

    private void updateCostExpandedChild(Node child, Node father, VAction vAct){
        if(!values.containsKey(child.getState())) {
            searchHelper.updateHeuristic(child, father, vAct, h);
        }else{
            //int cost = vAct.cost;
            //if(vAct.isNondeterministic) cost += 1;
            searchHelper.updateCost(child, father,vAct,values.get(child.getState()));
        }
    }

    private void update(Node n){
        int act = greedyAction(n);
        n.greedyAction = act;
        if(!n.successors.containsKey(act)){
            return;
        }
        long nValue = qDead(n, act);
    	/*if(!n.successors.containsKey(act)) return;
    	ArrayList<Node> succs = n.successors.get(act);
        //Add costs of the descendants
    	for(Node succ : succs){
            if(values.containsKey(succ.getState())){
                n.value += values.get(succ.getState());
            }else{
                n.value += succ.getH();
            }
    	}
    	values.put(n.getState(), n.value);*/
        n.value = nValue;
        values.put(n.getState(), nValue);
    }

    private long qValue(Node n, int act){
        long nValue = 0;
        ArrayList<Node> succs = n.successors.get(act);
        nValue += problem.cost[act];
        //Add costs of the descendants
        for(Node succ : succs){
            if(values.containsKey(succ.getState())){
                succ.value= values.get(succ.getState());
                nValue += succ.value;
            }else{
                nValue += succ.getH();
            }
        }
        return nValue;
    }
    
    private long qValueMax(Node n, int act){
        long nValue = 0;
        ArrayList<Node> succs = n.successors.get(act);
        nValue += problem.cost[act];
        //Add costs of the descendants
        for(Node succ : succs){
            if(values.containsKey(succ.getState())){
                succ.value= values.get(succ.getState());
                if(nValue < succ.value) nValue = succ.value;
            }else{
                if(nValue < succ.getH()) nValue = succ.getH();
            }
        }
        return nValue;
    }
    
    private long qDead(Node n, int act){
    	if(deadEndSuccessors(n)){
    		return qValue(n, act);
    	}else{
    		return qValueMax(n,act);
    	}
    }

    public void pickNextState(Node n){
        //Random r = new Random();
        ArrayList<Node> succs = n.successors.get(n.greedyAction);
        for(Node succ : succs){
            if(!solved(succ.getState())) fringe.add(succ);
        }
        //return succs.get(r.nextInt(succs.size()));
    }

    private int greedyAction(Node n){
        int action = n.greedyAction;
        /*Problem: two nondet successors are goal...and the other action also minimizes the value*/
        long value = n.value;
        for(int act : n.successors.keySet()){
            ArrayList<Node> succs = n.successors.get(act);
            //Add costs of the descendants
            long aux = 0L;
            for(Node succ : succs){
                if(values.containsKey(succ.getState())){
                    aux += values.get(succ.getState());
                }else{
                    aux += succ.getH();
                }
            }
            if(aux + problem.cost[act] < value){
                value = aux + problem.cost[act];
                action = act;
                //n.value = aux;
                //n.greedyAction = act;
            }
        }
        return action;
    }
}
