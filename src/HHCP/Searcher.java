package HHCP;

import simulator.Simulator;

import java.util.*;

/**
 * Created by ignasi on 15/05/17.
 */
public class Searcher {

    private Problem problem;
    private HashSet<BitSet> visited = new HashSet<BitSet>();
    private HashSet<BitSet> seen = new HashSet<BitSet>();
    private Stack<BitSet> open = new Stack<BitSet>();
    private HashSet<BitSet> DeadEnds = new HashSet<BitSet>();
    private HashMap<BitSet, Integer> forbiddenActions = new HashMap<BitSet, Integer>();
    private PriorityQueue<Node> fringe;
    private Heuristic h;
    private PartialPolicy policyP = new PartialPolicy();

    public Searcher(Problem p){
        problem = p;
        boolean deadEndsFound = false;
        h = new Heuristic(p);
        double startTime = System.currentTimeMillis();
        boolean modified = true;
        while(modified){
            modified = false;
            open.add(p.getInitState());
            HashMap<BitSet, Integer> parentAction = new HashMap<>();
            while(!open.isEmpty()){
                BitSet s = open.pop();
                if(!entails(s, problem.getGoal()) && !seen.contains(s)){
                    seen.add(s);
                    if(policyP.find(s)<0){
                        //System.out.println("State with no solution found.");
                        if(GenPlanPairs(s)){
                            modified = true;
                            //Mark State-Action Pairs
                            markStateActions();
                        }else {
                            System.out.println("Adding to Dead End Set the state: " + s.toString());
                            if(parentAction.containsKey(s)) forbiddenActions.put(regressStateAction(s, parentAction.get(s)), parentAction.get(s));
                            deadEndsFound=true;
                        }
                    }
                    int indexAction = policyP.find(s);
                    //New verification: verify that the new pair is not marked yet!
                    if(!policyP.valid(s)){
                    	//If it is not marked...put it on the open list
                    	/*if(indexAction == 198){
                    		System.out.println(problem.getAction(parentAction.get(s)).getName());
                    		System.out.println("Fatal moment");
                    	}*/
                        applyAction(indexAction, s, parentAction);
                        modified = false;
                    }/*else{
                    	System.out.println("Solved Path: expanding new path from " + problem.getAction(indexAction).getName());
                    }*/
                }
            }
            //TODO: What to do with weak problems?
            if(deadEndsFound){
                modified = true;
                processDeadEnds();
                deadEndsFound = false;
                visited.clear();
                seen.clear();
            }
        }
        //GenPlanPairs(problem.getInitState());
        double endTime = System.currentTimeMillis();
        System.out.println("Planner time: " + (endTime - startTime) + " Milliseconds");
        printPolicy(p.getInitState());
        //Simulator sim = new Simulator(policyP, p.getInitState(), problem);
    }

    private BitSet regressStateAction(BitSet s, Integer action) {
        BitSet ancestor = (BitSet) s.clone();
        VAction a = problem.getAction(action);
        for (int p = a.preconditions.nextSetBit(0); p >= 0; p = a.preconditions.nextSetBit(p+1)) {
            //for(int p : a.getPreconditions()){
            ancestor.set(p);
        }
        boolean appliedEffect = true;
        for(VEffect e : a.getEffects()){
            for(int eff : e.getAddList()){
                if(ancestor.get(eff)){
                    ancestor.set(eff,false);
                }else{
                    appliedEffect = false;
                }
            }
            if(appliedEffect){
                for(int c : e.getCondition()) ancestor.set(c);
            }
        }
        return ancestor;
    }

    private void markStateActions() {
        boolean changed = true;
        while(changed){
            changed = false;
            for(BitSet bs : policyP.iteratorStatesActions()){
                if(entails(bs, problem.getGoal()) || !policyP.marked.get(bs)) continue;
                //TODO:correct find operation. Use tries?
                int indexAction = policyP.find(bs);
                VAction a = problem.getAction(indexAction);
                //Verify for each effect 2 conditions:
                ArrayList<BitSet> successors = new ArrayList<BitSet>();
                if(a.isNondeterministic) {
                    for (VEffect e : a.getEffects()) {
                        BitSet s = (BitSet) bs.clone();
                        applyEffect(s, e);
                        successors.add(s);
                    }
                }else{
                    BitSet s = (BitSet) bs.clone();
                    for(VEffect e : a.getEffects()) {
                        applyEffect(s, e);
                    }
                    successors.add(s);
                }
                /*With the new states verify the 2 conditions:
                1 At least one successor is in the policy:
                2 States returned are marked.
                If not children or goal nodes: remain marked true
                */
                for(BitSet successor : successors){
                    if(entails(successor, problem.getGoal())) continue;
                    //if(!policyP.marked.containsKey(successor) || !policyP.marked.get(successor)){
                    if(!policyP.valid(successor)){
                        policyP.marked.put(bs, false);
                        //policyP.partial.remove(bs);
                        changed = true;
                    }
                }
            }
        }
    }

    private void applyEffect(BitSet s, VEffect e){
        for(int indexEffect : e.getDelList()){
            s.set(indexEffect, false);
        }
        for(int indexEffect : e.getAddList()){
            s.set(indexEffect);
        }
    }

    private void applyAction(int indexAction, BitSet s, HashMap<BitSet, Integer> parentAction){
        VAction a = problem.getAction(indexAction);
        if(a.isNondeterministic){
            for(VEffect e : a.getEffects()){
                BitSet s2 = (BitSet) s.clone();
                applyEffect(s2, e);
                parentAction.put(s2, indexAction);
                Node n = new Node(s2);
                n.fixedPoint(n, problem.vAxioms);
                open.push(n.getState());
            }
        }else{
            BitSet s2 = (BitSet) s.clone();
            for(VEffect e : a.getEffects()){
                applyEffect(s2, e);
            }
            parentAction.put(s2, indexAction);
            open.push(s2);
        }
    }

    private void printPolicy(BitSet initState) {
        //Imprimir politica resultado.
        //DirectedMultigraph<String, String> graph;
        System.out.println("Printing solution:");
        Solution sol = new Solution(policyP, initState, problem);
    }

    private void processDeadEnds() {
        //Get generalized dead-end
        policyP.clear();
    }

    private boolean entails(BitSet s, int[] goal) {
        boolean ret = true;
        for(int i : goal){
            if(!s.get(i)) return false;
        }
        return ret;
    }

    public boolean GenPlanPairs(BitSet initState){
        boolean solution = false;
        Comparator<Node> comparator = new NodeComparator();
        fringe = new PriorityQueue<Node>(100, comparator);
        Node initNode = new Node(initState);
        fringe.add(initNode);
        visited.clear();
        while(!solution) {
            if(fringe.isEmpty()){
                System.out.println("No weak plan found.\nThe initial State for this search may have caused a Dead-end.");
                DeadEnds.add(initState);
                return false;
            }
            Node node = fringe.poll();
            //if(node.indexAction != -1) System.out.println("Applied action: " + problem.getAction(node.indexAction).getName());
            if(visited(node)) continue;
            visited.add(node.getState());
            //TODO: isSolvedNode(node)?
            if(node.holds(problem.getGoal()) ){
                solution = true;
                //printPlan(node);
                //System.out.println("Weak solution found.");
                RegressPlan(node);
                //System.out.println("Regressed weak plan.");
                //solution=true;
            }
            for(VAction va : getApplicableActions(node)){
                if(forbiddenActions.containsKey(node.getState()) && forbiddenActions.get(node.getState()) == va.index)
                    continue;
                if(va.isNondeterministic){
                	/*if(va.index==89){
                		System.out.println("");
                	}*/
                    for(Node n : node.applyNonDeterministicAction(va, problem.vAxioms)){
                        //Review condition of adding the new state:
                        if(!DeadEnds.contains(n.getState())) {
                            updateHeuristic(n, node, va);
                            fringe.add(n);
                        }else{
                            //Add this transition to the forbidden action state pair
                            forbiddenActions.put(node.getState(), va.index);
                        }
                    }
                }else{
                    Node n = node.applyDeterministicAction(va);
                    if(!DeadEnds.contains(n.getState())){
                        updateHeuristic(n, node, va);
                        fringe.add(n);
                    }else{
                        //Add this transition to the forbidden action state pair
                        forbiddenActions.put(node.getState(), va.index);
                    }
                }
            }
        }
        //Review termination conditions
        return true;
    }

	private boolean isSolvedNode(Node node) {
		return policyP.valid(node.getState());
	}

	private void updateHeuristic(Node child, Node father, VAction va) {
        child.setCost(father.getCost() + va.cost);
        //System.out.println("Expanding action: " + va.getName());
        //System.out.println("In state: " + problem.printState(father.getState()));
        child.setHeuristic(h.getValue(child.getState(), va));
        //System.out.println("With heuristic: " + child.getH());
    }

    private void RegressPlan(Node node){
        //BitSet r = (BitSet) problem.getGoalSet().clone();
    	BitSet r = (BitSet) node.getState().clone();
        while(node.parent != null){
            //Regress the action here
        	//System.out.println("Regressing action: " + problem.getAction(node.indexAction).getName());
            VAction a = problem.getAction(node.indexAction);
            if(node.axioms != null) regressAxioms(node, r);
            for (int p = a.preconditions.nextSetBit(0); p >= 0; p = a.preconditions.nextSetBit(p+1)) {
                r.set(p);
            }
            regressNode(a,node,r);
            policyP.put((BitSet) r.clone(), node.indexAction);
            node = node.parent;
        }
    }

    private void regressAxioms(Node node, BitSet r) {
    	for (int i=node.axioms.size()-1; i>=0;i--) {
    		int index = node.axioms.get(i);
    		VAction ax = problem.getAction(index);
        	for (int p = ax.preconditions.nextSetBit(0); p >= 0; p = ax.preconditions.nextSetBit(p+1)) {
                r.set(p);
            }
        	for(VEffect e : ax.getEffects()){
                for(int eff : e.getAddList()){
                    if(r.get(eff)){
                    	r.set(eff,false);
                    }
                }
            }
    	}
	}

	private void regressNode(VAction a, Node node, BitSet r){
        if(a.isNondeterministic){
            VEffect e = a.getEffects().get(node.indexEffect);
            if(e.getCondition() != null) {
                for (int c : e.getCondition()) r.set(c);
            }
            for (int eff : e.getAddList()) {
                if (r.get(eff)) {
                    r.set(eff, false);
                }
            }
        }else{
            for(VEffect e : a.getEffects()){
                for(int c : e.getCondition()) r.set(c);
                for(int eff : e.getAddList()){
                    if(r.get(eff)){
                        r.set(eff,false);
                    }
                }
            }
        }
    }

    private void printPlan(Node node) {
        System.out.println("Printing solution:");
        ArrayList<String> solution = new ArrayList<String>();
        while(node.parent != null){
            solution.add(node.parentAction);
            node = node.parent;
        }
        for(int i = solution.size(); i>0; i--){
            System.out.println(solution.get(i-1));
        }
    }

    private boolean visited(Node node) {
        if(visited.contains(node.getState())){
            return true;
        }else{
            return false;
        }
    }

    private ArrayList<VAction> getApplicableActions(Node node) {
        //System.out.println("Applicable actions in: " + problem.printState(node.getState()));
        ArrayList<VAction> retList = new ArrayList<VAction>();
        /*problem.getVaList().stream()
                .filter(s -> ((s.getName().s) && (node.holds(s.getPreconditionArray()))))
                .forEach(retList::add);*/
        for(VAction va : problem.getVaList()){
        	if(va.getName().startsWith("K-axiom-")) continue;
            if(node.holds(va.getPreconditionArray())){
                retList.add(va);
                //System.out.println(va.getName());
            }

        }
        return retList;
    }
}
