package HHCP;

import java.util.*;

/**
 * Created by ignasi on 11/09/17.
 */
public class reMaxProb {

    private HashSet<BitSet> solved = new HashSet<BitSet>();
    private HashSet<BitSet> solvedOld = new HashSet<BitSet>();
    private Problem problem;
    private HashMap<BitSet, Float> visited;
    private HashSet<BitSet> deadEnds = new HashSet<BitSet>();
    private PriorityQueue<fNode> fringe;
    private HashMap<BitSet, ArrayList<Integer>> forbiddenActionPairs = new HashMap<BitSet, ArrayList<Integer>>();
    private HashMap<BitSet, Float> values = new HashMap<BitSet, Float>();
    private HashMap<BitSet, Float> valuesNew = new HashMap<BitSet, Float>();
    private HashMap<BitSet, Float> probabilities = new HashMap<BitSet, Float>();
    private PartialPolicy policyP = new PartialPolicy();
    private PartialPolicy policyOld = new PartialPolicy();
    private float dValue = 100000000000f;
    private HashSet<BitSet> avoidable = new HashSet<BitSet>();
    private float epsilon = 0.005f;
    private HashSet<BitSet> humanGenStates = new HashSet<BitSet>();

    public reMaxProb(Problem p, PartialPolicy policy, HashMap<BitSet, Float> valueHash, HashSet<BitSet> s) {
        problem = p;
        solvedOld = s;
        policyOld = policy;
        values = valueHash;
        double startTime = System.currentTimeMillis();
        while(!solved.contains(p.getInitState())){
            //genWeakSolution(p.getInitState());
            trial(p.getInitState());
        }
        double endTime = System.currentTimeMillis();
        System.out.println("Expected cost of the solution: " + values.get(p.getInitState()));
        System.out.println("Probability of reaching the goal (without human help): " + probabilities.get(p.getInitState()));
        System.out.println("Expected cost of the solution: " + valuesNew.get(p.getInitState()));
        searchHelper.printStats(policyP, startTime, endTime, p);
        searchHelper.printPolicy(p.getInitState(), policyP, p);
        //Simulator sim = new Simulator(policyP, p.getInitState(), problem, heuristicP);
    }

    private void trial(BitSet initState){
        BitSet s = (BitSet) initState.clone();
        Comparator<fNode> comparator = new fNodeComparator();
        fringe = new PriorityQueue<fNode>(100, comparator);
        //HashSet<BitSet> visited = new HashSet<BitSet>();
        visited = new HashMap<BitSet, Float>();
        fNode node = searchHelper.initLayers(new fNode(s), problem);
        node.setHeuristic(values.get(node.getState()));
        //fringe.add(initialNode);
        while(!node.holds(problem.getGoal()) && !solved(node.getState())) {
            fringe.clear();
            if (visited.containsKey(node.getState())){
                continue;
            }
            visited.put(node.getState(), node.getCost());
            expand(node);
            if(node.successors.isEmpty()){
                //node.value = Math.min();
                update(node);
                if(!node.successors.isEmpty() && successorsSolved(node)){
                    //System.out.println("Leaf states found.");
                    update(node);
                    regressPlan(node);
                    break;
                }
                addForbiddenAction((BitSet) node.parent.getState().clone(), node.indexAction);
                break;
            }
            update(node);
            pickNextState(node);
            if(successorsSolved(node)){
                //System.out.println("Leaf states found.");
                update(node);
                regressPlan(node);
                break;
            }
            node = searchHelper.initLayers(fringe.poll(), problem);
            if (node.holds(problem.getGoal()) || solved(node.getState()) ) {
                //System.out.println("Solution found");
                regressPlan(node);
                break;
            }
        }
    }

    private boolean successorsSolved(fNode node) {
        /*TODO: must test all descendants or only the greedy action descendants?*/
        boolean sSolved = true;
        for(fNode successor : node.successors.get(node.greedyAction)){
            if(!solved(successor.getState())) return false;
        }
        return sSolved;
    }

    private void regressPlan(fNode node) {
        //boolean flag = true;
        //pendentState = null;
        if(node.holds(problem.getGoal())){
            if(node.getState().get(problem.humanIndex)) {
                probabilities.put((BitSet) node.getState().clone(), 0f);
                values.put((BitSet) node.getState().clone(), dValue);
                node.value = dValue;
                solved.add((BitSet) node.getState().clone());

            }else{
                probabilities.put((BitSet) node.getState().clone(), 1f);
                values.put((BitSet) node.getState().clone(), 0f);
                node.value = 0;
                solved.add((BitSet) node.getState().clone());
            }
            node.value = 0;
            solved.add((BitSet) node.getState().clone());
            //values.put((BitSet) node.getState().clone(), 0f);
        }else{
            node.greedyAction = greedyAction(node);
            if(node.successors.containsKey(node.greedyAction)){
                if(checkSolved(node)){
                    policyP.put((BitSet) node.getState().clone(), node.greedyAction);
                    updateProbabilities(node);
                }
            }
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
                updateProbabilities(node);
            }
        }
    }

    private void updateProbabilities(fNode node) {
        float aux = 0;
        ArrayList<fNode> succs = node.successors.get(node.greedyAction);
        for(fNode succ : succs){
            aux += (probabilities.get(succ.getState()) / succs.size());
        }
        probabilities.put((BitSet) node.getState().clone(), aux);
        update(node);
        valuesNew.put((BitSet) node.getState().clone(), node.value);
    }

    private boolean solved(BitSet state) {
        boolean b = solved.contains(state);
        return b;
    }

    private boolean checkSolved(fNode n) {
        boolean rv = true;
        Stack<fNode> open = new Stack<fNode>();
        Stack<fNode> closed = new Stack<fNode>();
        if(!solved.contains(n.getState())){
            open.push(n);
        }
        while(!open.isEmpty()){
            fNode s = open.pop();
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
            ArrayList<fNode> succs = s.successors.get(s.greedyAction);
            for(fNode succ : succs){
                if(!solved(succ.getState()) && !open.contains(succ) && !closed.contains(succ)){
                    if(succ.holds(problem.getGoal())){
                        solved.add((BitSet) succ.getState().clone());
                        values.put((BitSet) succ.getState().clone(), 0f);
                    }else {
                        //pendentState = (BitSet) succ.getState().clone();
                        return false;
                        //open.push(succ);
                    }
                }
            }
        }
        if(rv){
            //label relevant states
            while(!closed.isEmpty()){
                fNode sPrima = closed.pop();
                updateFinal(sPrima);
                solved.add((BitSet) sPrima.getState().clone());
                //updateWave(sPrima);
            }
        }else{
            //update states with residuals and ancestors
            while(!closed.isEmpty()){
                fNode sPrima = closed.pop();
                update(sPrima);
            }
        }
        return rv;
    }

    private void updateFinal(fNode n) {
        int act = n.greedyAction;
        if(!n.successors.containsKey(act)){
            return;
        }
        float nValue = qFPUDE(n, act);
        n.value = nValue;
        values.put(n.getState(), nValue);
    }

    private float residual(fNode n){
        //Take the minimal action
        float residual = 0f;
        int action = greedyAction(n);
        if(!n.successors.containsKey(action)) return 1;
        //Verify next line!!!!
        float succValue = qFPUDE(n, action);
        if((succValue + problem.cost[action]) < values.get(n.getState())){
            residual = Math.abs((succValue + problem.cost[action]) - values.get(n.getState()));
            if(residual <= epsilon){
                //System.out.println("Converged state");
                return 0;
            }
        }
        return residual;
    }

    private void expand(fNode n){
        for(int action = n.getScheduledActions().nextSetBit(0); action >= 0; action = n.getScheduledActions().nextSetBit(action+1)){
            if(forbiddenActionPairs.containsKey(n.getState()) && (forbiddenActionPairs.get(n.getState()).contains(action))){
                continue;
            }
            VAction vAct = problem.getAction(action);
            ArrayList<fNode> listSucc = new ArrayList<fNode>();
            if(vAct.isNondeterministic || vAct.isObservation){
                ArrayList<fNode> successors = n.applyNonDeterministicAction(vAct,problem);
                for(fNode succ : successors){
                    updateCostExpandedChild(succ, n, vAct);
                    if(isDeadEnd(succ)){
                        processDeadEnds(succ, n, vAct);
                    }
                    listSucc.add(succ);
                    if(!solved(succ.getState()) && !n.visited.contains(succ.getState())){
                        //fringe.add(succ);
                    }
                    succ.addVisited(n.visited);
                }
            }else{
                fNode child = n.applyDeterministicAction(vAct, problem);
                if(n.visited.contains(child.getState())) continue;
                updateCostExpandedChild(child, n, vAct);
                child.setHeuristic(Math.min(dValue, child.getH()));
                listSucc.add(child);
                //!solved(child.getState()) &&
                if(!n.visited.contains(child.getState())){
                    //fringe.add(child);
                }
                child.addVisited(n.visited);
            }
            n.numberSuccessors += listSucc.size();
            if(!listSucc.isEmpty()) {
                n.successors.put(action, listSucc);
            }
        }
        if(n.successors.isEmpty()){
            addForbiddenAction((BitSet) n.parent.getState().clone(), n.indexAction);
            avoidable.add((BitSet) n.getState().clone());
        }
    }

    private void processDeadEnds(fNode child, fNode father, VAction vAct){
        deadEnds.add(child.getState());
        solved.add((BitSet) child.getState().clone());
        values.put((BitSet) child.getState().clone(), dValue);
        probabilities.put((BitSet) child.getState().clone(), 0f);
        child.setHeuristic(dValue);
        child.value = dValue;
        //fringe.add(child);
    }

    private boolean isDeadEnd(fNode succ){
        if(deadEnds.contains(succ.getState()) || succ.getH() >= Float.MAX_VALUE){
            //System.out.println("Dead-end state found.");
            //return true;
        }
        return false;
    }

    private void updateCostExpandedChild(fNode child, fNode father, VAction vAct){
        if(solvedOld.contains(child.getState())){
            searchHelper.updateCost(child, father,vAct,values.get(child.getState()));
        }else{
            child.setCost(father.getCost() + vAct.cost);
            child.setHeuristic(Float.MAX_VALUE);
            child.value = Float.MAX_VALUE;
            values.put(child.getState(), Float.MAX_VALUE);
        }
        /*
        if(!values.containsKey(child.getState())) {
            //searchHelper.updateHeuristic(child, father, vAct, h, dValue);
            child.setHeuristic(Float.MAX_VALUE);
        }else{
            searchHelper.updateCost(child, father,vAct,values.get(child.getState()));
        }*/
    }

    private void update(fNode n){
        int act = greedyAction(n);
        n.greedyAction = act;
        if(!n.successors.containsKey(act)){
            return;
        }
        float nValue = qFPUDE(n, act);
        n.value = nValue;
        values.put(n.getState(), nValue);
    }

    /*private float qAverage(fNode n, int act){
        float nValue = 0;
        ArrayList<fNode> succs = n.successors.get(act);
        nValue += problem.cost[act];
        //Add costs of the descendants
        for(fNode succ : succs){
            if(values.containsKey(succ.getState())){
                succ.value= values.get(succ.getState());
                nValue += (succ.value / succs.size());
            }else{
                nValue += (succ.getH() / succs.size());
            }
        }
        return nValue;
    }*/

    private float qFPUDE(fNode n, int act){
        float nValue = 0;
        ArrayList<fNode> succs = n.successors.get(act);
        nValue += problem.cost[act];
        //Add costs of the descendants
        for(fNode succ : succs){
            if(values.containsKey(succ.getState())){
                succ.value= values.get(succ.getState());
                nValue += (succ.value / succs.size());
            }else{
                nValue += (succ.getH() / succs.size());
            }
        }
        return Math.min(dValue, nValue);
    }

    private void addForbiddenAction(BitSet state, int action){
        if(forbiddenActionPairs.containsKey(state)) {
            HashSet<Integer> aux = new HashSet<Integer>(forbiddenActionPairs.get(state));
            aux.add(action);
            forbiddenActionPairs.put(state, new ArrayList<Integer>(aux));
        }else{
            HashSet<Integer> aux = new HashSet<Integer>();
            aux.add(action);
            forbiddenActionPairs.put(state, new ArrayList<Integer>(aux));
        }
    }

    private int greedyAction(fNode n){
        int action = n.greedyAction;
        float value = n.value;
        for(int act : n.successors.keySet()){
            float aux = qFPUDE(n, act);
            if(aux + problem.cost[act] < value){
                value = aux + problem.cost[act];
                action = act;
            }else if(aux + problem.cost[act] == value){
                action = policyOld.action(n.getState());
            }
            if(action < 0){
                action = act;
            }
        }
        return action;
    }

    public void pickNextState(fNode n){
        //int act = greedyAction(n);
        //n.greedyAction = act;
        ArrayList<fNode> succs = n.successors.get(n.greedyAction);
        for(fNode succ : succs){
            if(!solved(succ.getState())) fringe.add(succ);
        }
    }
}
