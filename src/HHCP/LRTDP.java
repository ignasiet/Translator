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
    private PartialPolicy policyP = new PartialPolicy();
    private HashMap<Integer, Integer> actionsCost = new HashMap<Integer, Integer>();
    private int bestSolution = Integer.MAX_VALUE;

    public LRTDP(Problem p, Problem heuristicP, ArrayList<String> l, JustificationGraph jG, String heuristic) {
        problem = p;
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

    //TODO: dead-ends and cycles, what to do?
    private void trial(BitSet initState) {
        Stack<Node> visited = new Stack<Node>();
        HashSet<BitSet> visitedStates = new HashSet<BitSet>();
        BitSet s = (BitSet) initState.clone();
        Comparator<Node> comparator = new NodeComparator();
        fringe = new PriorityQueue<Node>(100, comparator);
        Node initialNode = searchHelper.initLayers(new Node(s), problem);
        while(!initialNode.holds(problem.getGoal()) && !solved(initialNode.getState())){
            //Insert into visited
            visited.push(initialNode);
            visitedStates.add(initialNode.getState());
            //Check termination at goal states
            if(initialNode.holds(problem.getGoal())) break;
            //Pick best action and update hash
            expand(initialNode);
            int greedyAct = greedyAction(initialNode);
            Node greedySuccessor = pickNextState(initialNode);
            //initialNode.greedyAction = greedyAction();
            update(initialNode);
            //Obtain the best (heuristic) successor
            initialNode = searchHelper.initLayers(greedySuccessor, problem);
        }
        if(initialNode.holds(problem.getGoal())){
            initialNode.value = 0;
            solved.add((BitSet) initialNode.getState().clone());
            values.put((BitSet) initialNode.getState().clone(), 0);
        }
        System.out.println("End a trial");
        while(!visited.isEmpty()){
            Node n = visited.pop();
            update(n);
            if(!checkSolved(n)){
                break;
            }
            policyP.put((BitSet) n.getState().clone(), n.greedyAction);
        }
    }

    private void genWeakSolution(BitSet initState) {
        BitSet s = (BitSet) initState.clone();
        Comparator<Node> comparator = new NodeComparator();
        fringe = new PriorityQueue<Node>(100, comparator);
        HashSet<BitSet> visited = new HashSet<BitSet>();
        Node initialNode = searchHelper.initLayers(new Node(s), problem);
        fringe.add(initialNode);
        while(!initialNode.holds(problem.getGoal()) && !solved(initialNode.getState())) {
            if (fringe.isEmpty()) {
                System.out.println("No weak plan found.\nThe initial State for this search may have caused a Dead-end.");
                //break;
            }
            /*if(initialNode.getCost() > bestSolution){
                System.out.println("CUTOFF!");
                break;
            }*/
            Node node = searchHelper.initLayers(fringe.poll(), problem);
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
            update(node);
        }
    }

    private void driver(BitSet initState){
        BitSet s = (BitSet) initState.clone();
        HashSet<BitSet> visited = new HashSet<BitSet>();
        Node initialNode = searchHelper.initLayers(new Node(s), problem);
        while(!initialNode.holds(problem.getGoal()) && !solved(initialNode.getState())) {
            visited.add(initialNode.getState());
            //Check termination at goal states
            if(initialNode.holds(problem.getGoal())) break;
            expand(initialNode);
            int a = greedyAction(initialNode);
            update(initialNode);
            Node greedySuccessor = pickNextState(initialNode);
            //Obtain the best (heuristic) successor
            initialNode = searchHelper.initLayers(greedySuccessor, problem);
        }
        regressPlan(initialNode);
    }

    private void regressPlan(Node node) {
    	//boolean flag = true;
        if(node.holds(problem.getGoal())){
            node.value = 0;
            solved.add((BitSet) node.getState().clone());
            values.put((BitSet) node.getState().clone(), 0);
        }
        while(node.parent != null){
            if(node.parent != null) node.parent.greedyAction = node.indexAction;
            node = node.parent;
            update(node);
            //if(!flag) continue;
            if(!checkSolved(node)){
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
        			open.push(succ);
        		}
        	}
        }
        if(rv){
            //label relevant states
            while(!closed.isEmpty()){
                Node sPrima = closed.pop();
                solved.add((BitSet) sPrima.getState().clone());
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
    
    private int residual(Node n){
    	//Take the minimal action
    	int residual = 0;
    	int action = greedyAction(n);
    	if(!n.successors.containsKey(action)) return 1;
        int succValue = qValue(n, action);
        if((succValue + problem.cost[action]) < values.get(n.getState())){
            residual = Math.abs((succValue + problem.cost[action]) - values.get(n.getState()));
        }
    	return residual;
    }

    private int getValue(Node n){
        if(values.containsKey(n.getState())){
            return values.get(n.getState());
        }
        return Integer.MAX_VALUE;
    }

    private void initHeuristic(Problem heuristicP, ArrayList<String> l, JustificationGraph jG, String heuristic) {
        if(!l.isEmpty()){
            landmarks = new ArrayList<>();
        }
        h = new Heuristic(heuristicP, landmarks, jG, heuristic);
        h.useCosts(heuristicP.cost);
    }

    private void expand(Node n){
        //PriorityQueue<Node> childrenFringe = new PriorityQueue<Node>(100, comparator);
        //int maxH = Integer.MAX_VALUE;
        for(int action = n.getScheduledActions().nextSetBit(0); action >= 0; action = n.getScheduledActions().nextSetBit(action+1)){
            VAction vAct = problem.getAction(action);
            ArrayList<Node> listSucc = new ArrayList<Node>();
            if(vAct.isNondeterministic || vAct.isObservation){
                ArrayList<Node> successors = n.applyNonDeterministicAction(vAct,problem);
                for(Node succ : successors){
                    updateCostExpandedChild(succ, n, vAct);
                    listSucc.add(succ);
                    if(!solved(succ.getState())) fringe.add(succ);
                }
                /*for(Node succ : listSucc){
                    succ.setHeuristic(hAdd);
                    if(!solved(succ.getState())) fringe.add(succ);
                }*/
            }else{
                Node child = n.applyDeterministicAction(vAct, problem);
                if(n.parent != null && child.getState().equals(n.parent.getState())){
                    continue;
                }
                updateCostExpandedChild(child, n, vAct);
                listSucc.add(child);
                fringe.add(child);
            }
            n.successors.put(action, listSucc);
        }
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
        if(!n.successors.containsKey(act)) return;
        int nValue = qValue(n, act);
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
    
    private int qValue(Node n, int act){
        int nValue = 0;
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

    public Node pickNextState(Node n){
        Random r = new Random();
        ArrayList<Node> succs = n.successors.get(n.greedyAction);
        for(Node succ : succs){
        	if(!solved(succ.getState())) return succ;
        }
        return succs.get(r.nextInt(succs.size()));
    }

    private int greedyAction(Node n){
        int action = n.greedyAction;
        for(int act : n.successors.keySet()){
            ArrayList<Node> succs = n.successors.get(act);
            //Add costs of the descendants
            int aux = 0;
            for(Node succ : succs){
                if(values.containsKey(succ.getState())){
                    aux += values.get(succ.getState());
                }else{
                    aux += succ.getH();
                }
            }
            if(aux + problem.cost[act] < n.value){
                action = act;
                //n.value = aux;
                //n.greedyAction = act;
            }
        }
        return action;
    }
}
