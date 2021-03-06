package HHCP;

import java.util.*;

/**
 * Created by ignasi on 11/09/17.
 */
public class LCGRTDP {

    private HashSet<BitSet> solved = new HashSet<BitSet>();
    private Problem problem;
    private Heuristic h;
    private HashMap<BitSet, Long> visited;
    private HashSet<BitSet> deadEnds = new HashSet<BitSet>();
    private ArrayList<Integer> landmarks;
    private PriorityQueue<Node> fringe;
    private HashMap<BitSet, Integer> forbiddenActionPairs = new HashMap<BitSet, Integer>();
    private HashMap<BitSet, ArrayList<Node>> nextStates = new HashMap<BitSet, ArrayList<Node>>();
    private HashMap<BitSet, Long> values = new HashMap<BitSet, Long>();
    private PartialPolicy policyP = new PartialPolicy();
    //private HashMap<BitSet, Integer> GreedyEnvelope = new HashMap<BitSet, Integer>();
    private long dValue = 400000000000l;
    private BitSet pendentState;
    private HashMap<BitSet, Integer> numberDE = new HashMap<>();

    public LCGRTDP(Problem p, Problem heuristicP, ArrayList<String> l, JustificationGraph jG, String heuristic, long cost) {
        problem = p;
        dValue = cost;
        initHeuristic(heuristicP, l, jG, heuristic);
        double startTime = System.currentTimeMillis();
        while(!solved.contains(p.getInitState())){
            //trial(p.getInitState());
            genWeakSolution(p.getInitState());
        }
        double endTime = System.currentTimeMillis();
        System.out.println("Expected cost of the solution: " + values.get(p.getInitState()));
        searchHelper.printStats(policyP, startTime, endTime, p);
        searchHelper.printPolicy(p.getInitState(), policyP, p);
    }

    private void trial(BitSet initState){
        BitSet s = (BitSet) initState.clone();
        Comparator<Node> comparator = new NodeComparator();
        fringe = new PriorityQueue<Node>(100, comparator);
        //HashSet<BitSet> visited = new HashSet<BitSet>();
        visited = new HashMap<BitSet, Long>();
        Node initialNode = searchHelper.initLayers(new Node(s), problem);
        initialNode.setHeuristic(searchHelper.getHeuristic(initialNode, h));
        //fringe.add(initialNode);
        while(!initialNode.holds(problem.getGoal()) && !solved(initialNode.getState())) {
            fringe.clear();
            if (visited.containsKey(initialNode.getState())){
                solved.add((BitSet) initialNode.getState().clone());
                values.put((BitSet) initialNode.getState().clone(), dValue);
            }
            visited.put(initialNode.getState(), initialNode.getCost());
            if (initialNode.holds(problem.getGoal()) || solved(initialNode.getState()) ) {
                System.out.println("Solution found");
                regressPlan(initialNode);
                break;
            }
            expand(initialNode);
            if(initialNode.successors.isEmpty()){
                //node.value = Math.min();
                update(initialNode);
                if(!initialNode.successors.isEmpty() && successorsSolved(initialNode)){
                    System.out.println("Leaf states found.");
                    update(initialNode);
                    regressPlan(initialNode);
                    break;
                }
                solved.add((BitSet) initialNode.getState().clone());
                values.put((BitSet) initialNode.getState().clone(), dValue);
                break;
                //continue;
            }
            update(initialNode);
            pickNextState(initialNode);
            if(successorsSolved(initialNode)){
                System.out.println("Leaf states found.");
                update(initialNode);
                regressPlan(initialNode);
                break;
            }
            initialNode = searchHelper.initLayers(fringe.poll(), problem);
        }
    }

    private void genWeakSolution(BitSet initState) {
        BitSet s = (BitSet) initState.clone();
        Comparator<Node> comparator = new NodeComparator();
        fringe = new PriorityQueue<Node>(100, comparator);
        //HashSet<BitSet> visited = new HashSet<BitSet>();
        visited = new HashMap<BitSet, Long>();
        Node initialNode = searchHelper.initLayers(new Node(s), problem);
        initialNode.setHeuristic(searchHelper.getHeuristic(initialNode, h));
        fringe.add(initialNode);
        while(!initialNode.holds(problem.getGoal()) && !solved(initialNode.getState())) {
            if (fringe.isEmpty()) {
                System.out.println("No weak plan found.\nThe initial State for this search may have caused a Dead-end.");
                update(initialNode);
                //solved.add((BitSet) initialNode.getState().clone());
                //Settle for the best children solved
                //settleSolution(initialNode);
                break;
            }
            Node node = searchHelper.initLayers(fringe.poll(), problem);
            //Node node = searchHelper.initLayers(pickNextState(n)), problem)-
            //if(node.parent != null) node.parent.greedyAction = node.indexAction;

            /*if(visited.containsKey(node.getState())){
                if(solved.contains(node.getState())){
                    fringe.clear();
                    System.out.println("Solution found");
                    regressPlan(node);
                    break;
                }
                //Here a repeated node is found with higher cost than before...discard
                if(visited.get(node.getState()) < node.getCost()){
                    //solved.add((BitSet) node.getState().clone());
                    values.put((BitSet) node.getState().clone(), dValue);
                    continue;
                }
            }*/

            /*if (visited.containsKey(node.getState())) {
                if(visited.get(node.getState()) < node.getCost()){
                    //solved.add((BitSet) node.getState().clone());
                    values.put((BitSet) node.getState().clone(), dValue);
                    continue;
                }
                continue;
            }*/
            visited.put(node.getState(), node.getCost());

            if (node.holds(problem.getGoal()) || solved(node.getState()) ) {
                fringe.clear();
                System.out.println("Solution found");
                regressPlan(node);
                break;
            }
            int size = fringe.size();
            expand(node);
            if(node.successors.isEmpty() || size == fringe.size()){
                update(node);
                if(!node.successors.isEmpty() && successorsSolved(node)){
                    fringe.clear();
                    System.out.println("Leaf states found.");
                    update(node);
                    regressPlan(node);
                    break;
                }
                //solved.add((BitSet) node.getState().clone());
                //values.put((BitSet) node.getState().clone(), dValue);
                break;
            }
            update(node);
            //pickNextState(node);
            if(successorsSolved(node)){
                System.out.println("Leaf states found.");
                fringe.clear();
                update(node);
                regressPlan(node);
                break;
            }
        }
    }

    private boolean someChildrenSolved(int sizeNode, int size){
        return sizeNode + size > fringe.size();
    }

    private boolean successorsSolved(Node node) {
        /*TODO: must test all descendants or only the greedy action descendants?*/
        boolean sSolved = true;
        for(Node successor : node.successors.get(node.greedyAction)){
            if(!solved(successor.getState())) return false;
        }
        return sSolved;
    }

    private void settleSolution(Node node){
        while(policyP.action(node.getState()) < 0) {
            expand(node);
            int bestAction = greedyAction(node);
            policyP.put((BitSet) node.getState().clone(), node.greedyAction);
            node = node.successors.get(bestAction).get(0);
        }
    }

    private void regressPlan(Node node) {
        //boolean flag = true;
        pendentState = null;
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
            //if(problem.getAction(node.indexAction).isNondeterministic) {
            if (!checkSolved(node)) {
                //node = null;
                break;
            } else {
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
                        pendentState = (BitSet) succ.getState().clone();
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
                updateFinal(sPrima);
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

    private void updateFinal(Node n) {
        int act = n.greedyAction;
        if(!n.successors.containsKey(act)){
            return;
        }
        long nValue = qDead(n, act);
        n.value = nValue;
        values.put(n.getState(), nValue);
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
        //Verify next line!!!!
        long succValue = qDead(n, action);
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
                    if(!solved(succ.getState())){
                        fringe.add(succ);
                    }
                    succ.addVisited(n.visited);
                }
            }else{
                Node child = n.applyDeterministicAction(vAct, problem);
                if(n.visited.contains(child.getState())) {
                    //continue;
                }
                if(n.parent != null && child.getState().equals(n.parent.getState())){
                    //continue;
                }
                updateCostExpandedChild(child, n, vAct);
                child.setHeuristic(Math.min(Long.MAX_VALUE, child.getH()));
                listSucc.add(child);
                if(!solved(child.getState()) && !n.visited.contains(child.getState())){
                    fringe.add(child);
                    //if(!visited.containsKey(child.getState()))
                }
                child.addVisited(n.visited);
                //fringe.add(child);
            }
            n.numberSuccessors += listSucc.size();
            if(!listSucc.isEmpty()) {
                n.successors.put(action, listSucc);
            }
        }
        if(n.successors.isEmpty()){
            //System.out.println("Childless state.");
            solved.add((BitSet) n.getState().clone());
            values.put((BitSet) n.getState().clone(), dValue);
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
            solved.add((BitSet) succ.getState().clone());
            values.put((BitSet) succ.getState().clone(), dValue);
            succ.setHeuristic(dValue);
            return true;
        }
        return false;
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
        //nValue += problem.cost[act];
        //Add costs of the descendants
        for(Node succ : succs){
            if(values.containsKey(succ.getState())){
                succ.value= values.get(succ.getState());
                if(nValue < succ.value) nValue = succ.value;
            }else{
                if(nValue < succ.getH()) nValue = succ.getH();
            }
        }
        nValue += problem.cost[act];
        return nValue;
    }
    
    private long qDead(Node n, int act){
    	if(deadEndChild(n, act)){
    		return qValue(n, act);
    	}else{
            //return qValue(n, act);
    		return qValueMax(n,act);
    	}
    }

    private boolean deadEndChild(Node node, int act) {
        boolean deadchild = false;
        for(Node successor : node.successors.get(act)){
            if(deadEnds.contains(successor.getState())) return true;
        }
        return deadchild;
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
        long value = n.value;
        for(int act : n.successors.keySet()){
            long aux = qDead(n, act);
            if(aux + problem.cost[act] < value){
                value = aux + problem.cost[act];
                action = act;
            }
        }
        return action;
    }

    private int greedyActionDepr(Node n){
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
