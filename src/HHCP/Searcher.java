package HHCP;

import oracle.jrockit.jfr.events.Bits;
import simulator.Simulator;

import java.lang.reflect.Array;
import java.util.*;

/**
 * Created by ignasi on 15/05/17.
 */
public class Searcher {

    private Problem problem;
    private Problem HProblem;
    private HashSet<BitSet> visited = new HashSet<BitSet>();
    private HashSet<BitSet> seen = new HashSet<BitSet>();
    private Stack<BitSet> open = new Stack<BitSet>();
    private HashSet<BitSet> DeadEnds = new HashSet<BitSet>();
    private HashMap<BitSet, Integer> forbiddenActions = new HashMap<BitSet, Integer>();
    private PriorityQueue<Node> fringe;
    private Heuristic h;
    private PartialPolicy policyP = new PartialPolicy();
    private ArrayList<Integer> landmarks;


    public Searcher(Problem p, Problem heuristicP, ArrayList<String> l){
        problem = p;
        HProblem = heuristicP;
        boolean deadEndsFound = false;
        if(!l.isEmpty()){
            landmarks = new ArrayList<>();
            for(String landmark : l){
                if(!p.getInitState().get(p.getPredicate(landmark))){
                    landmarks.add(p.getPredicate(landmark));
                }
            }
        }
        h = new Heuristic(heuristicP, landmarks);
        //Search starts!
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
                    }
                }
            }
            //markStateActions();
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
        System.out.println("==========================================================");
        System.out.println("Initial state solved " + policyP.valid(p.getInitState()));
        System.out.println("Results:");
        System.out.println("Planner time: " + (endTime - startTime) + " Milliseconds");
        System.out.println("Number of nodes: " + policyP.partial.size());
        System.out.println("Policy size: " + policyP.size());
        System.out.println("Number of states solved: " + policyP.marked.size());
        //printPolicy(p.getInitState());
        Simulator sim = new Simulator(policyP, p.getInitState(), problem);
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
            //CAUTION HERE! verify the conditional effect has been applied before regressing it!
            BitSet A = (BitSet) e.getAddList().clone();
            A.and(ancestor);
            if(A.equals(e.getAddList())){
                for(int i = e.getAddList().nextSetBit(0); i>=0; i= e.getAddList().nextSetBit(i+1)){
                    ancestor.set(i,false);
                }
                ancestor.or(e.getCondition());
            }
            /*else{
                appliedEffect = false;
            }*/
            /*for(int eff : e.getAddList()){
                if(ancestor.get(eff)){
                    ancestor.set(eff,false);
                }else{
                    appliedEffect = false;
                }
            }*/
            /*if(appliedEffect){
                //for(int c : e.getCondition()) ancestor.set(c);
                ancestor.or(e.getCondition());
            }*/
        }
        return ancestor;
    }

    private void markStateActions() {
        for(BitSet bs : policyP.marked.keySet()){
            policyP.marked.put(bs, true);
        }
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
        /*for(int indexEffect : e.getDelList()){
            s.set(indexEffect, false);
        }*/
        //Add operation between bitsets:
        s.or(e.getAddList());
        /*BitSet x = (BitSet) s.clone();
        x.xor(e.getDelList());*/
        for(int i = e.getDelList().nextSetBit(0);i>=0;i=e.getDelList().nextSetBit(i+1)){
            s.set(i, false);
        }
        //s.xor(e.getDelList());
        /*for(int indexEffect : e.getAddList()){
            s.set(indexEffect);
        }*/
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

    private boolean entails(BitSet s, BitSet goal) {
        BitSet A = (BitSet) goal.clone();
        A.and(s);
        return A.equals(goal);
        /*boolean ret = true;
        for(int i : goal){
            if(!s.get(i)) return false;
        }
        return ret;*/
    }

    public boolean GenPlanPairs(BitSet initState){
        boolean solution = false;
        Comparator<Node> comparator = new NodeComparator();
        fringe = new PriorityQueue<Node>(100, comparator);
        Node initNode = new Node(initState);
        h.getValue(initNode);
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
            //TODO: isSolvedNode(node)? check
            if(node.holds(problem.getGoal()) || policyP.valid(node.getState()) ){
                //solution = true;
                RegressPlan(node);
                break;
            }
            //TODO: Verify the selected action is not an axiom!
            if(!node.relaxedSolution.isEmpty()){
                VAction va = problem.getAction(node.preferredAction);
                addToFringe(va, node);
            }else {
                for (VAction va : getApplicableActions(node)) {
                    if (forbiddenActions.containsKey(node.getState()) && forbiddenActions.get(node.getState()) == va.index)
                        continue;
                    addToFringe(va, node);
                }
            }
        }
        //Review termination conditions
        return true;
    }

    private void addToFringe(VAction va, Node node){
        if (va.isNondeterministic) {
            ArrayList<Node> getSuccessorNodes = node.applyNonDeterministicAction(va, problem.vAxioms);
            for (Node n : getSuccessorNodes) {
                //Review condition of adding the new state:
                if (!DeadEnds.contains(n.getState())) {
                    /*if(visited.contains(n.getState())){
                        System.out.println();
                    }*/
                    updateHeuristic(n, node, va);
                    fringe.add(n);
                } else {
                    //Add this transition to the forbidden action state pair
                    forbiddenActions.put(node.getState(), va.index);
                }
            }
        } else {
            Node n = node.applyDeterministicAction(va);
            if (!DeadEnds.contains(n.getState())) {
                /*if(visited.contains(n.getState())){
                    va = HProblem.getAction(node.relaxedSolution.get(node.relaxedSolution.size()-2));
                    va = problem.getAction(va.getName());
                    if(!va.isNondeterministic) n = node.applyDeterministicAction(va);
                }*/
                updateHeuristic(n, node, va);
                fringe.add(n);
            } else {
                //Add this transition to the forbidden action state pair
                forbiddenActions.put(node.getState(), va.index);
            }
        }
    }

	private boolean isSolvedNode(Node node) {
		return policyP.valid(node.getState());
	}

	private void updateHeuristic(Node child, Node father, VAction va) {
        child.setCost(father.getCost() + va.cost);
        child.setHeuristic(h.getValue(child));
    }

    private void RegressPlan(Node node){
        //BitSet r = (BitSet) problem.getGoalSet().clone();
    	BitSet r = (BitSet) node.getState().clone();
        while(node.parent != null){
            /*Regress the action here
            Should we regress here?*/
            VAction a = problem.getAction(node.indexAction);
            //TODO: verify how axioms are regressed
            if(node.axioms != null) regressAxioms(node, r);
            //1 regress preconditions: put them all 1
            r.or(a.preconditions);
            /*for (int p = a.preconditions.nextSetBit(0); p >= 0; p = a.preconditions.nextSetBit(p+1)) {
                r.set(p);
            }*/
            //Regress effects
            regressNode(a,node,r);
            policyP.put((BitSet) r.clone(), node.indexAction);
            node = node.parent;
        }
    }

    private void regressAxioms(Node node, BitSet r) {
    	for (int i=node.axioms.size()-1; i>=0;i--) {
    		int index = node.axioms.get(i);
    		VAction ax = problem.getAction(index);
            r.or(ax.preconditions);
        	/*for (int p = ax.preconditions.nextSetBit(0); p >= 0; p = ax.preconditions.nextSetBit(p+1)) {
                r.set(p);
            }*/
            //Axioms have only one effect:
        	for(VEffect e : ax.getEffects()){
                //BitSet A = (BitSet) e.getAddList().clone();
                //A.and(r);
                for(int j = e.getAddList().nextSetBit(0); j>=0;j=e.getAddList().nextSetBit(j+1)){
                    //TODO: vvvv verify regression here! vvvvv
                    if(!node.parent.getState().get(j)){
                        r.set(j,false);
                    }
                    //r.set(j,false);
                }
                /*if(A.equals(e.getAddList())){

                }*/
                /*for(int eff : e.getAddList()){
                    if(r.get(eff)){
                    	r.set(eff,false);
                    }
                }*/
            }
    	}
	}

	private void regressNode(VAction a, Node node, BitSet r){
        //TODO: verify that the bitset r does not delete what was at node.getState()
        if(a.isNondeterministic){
            VEffect e = a.getEffects().get(node.indexEffect);
            /*if(e.getCondition() != null) {
                //for (int c : e.getCondition()) r.set(c);
                //Add operation between bitsets:
                r.or(e.getCondition());
            }*/
            //BitSet A = (BitSet) e.getAddList().clone();
            //A.and(r);
            /*if(A.equals(e.getAddList())){

            }*/
            r.or(e.getCondition());
            for(int j = e.getAddList().nextSetBit(0); j>=0;j=e.getAddList().nextSetBit(j+1)){
                //TODO: vvvv verify regression here! vvvvv
                if(!node.parent.getState().get(j)){
                    r.set(j,false);
                }
                //r.set(j,false);
            }
        }else{
            for(VEffect e : a.getEffects()){
                //for(int c : e.getCondition()) r.set(c);
                //Verify the effect was applied:
                if(e.getCondition().isEmpty()){
                    for(int j = e.getAddList().nextSetBit(0); j>=0;j=e.getAddList().nextSetBit(j+1)){
                        //TODO: vvvv verify regression here! vvvvv
                        if(!node.parent.getState().get(j)){
                            r.set(j,false);
                        }
                        //r.set(j,false);
                    }
                }else{
                    BitSet A = (BitSet) e.getAddList().clone();
                    A.and(r);
                    if(A.equals(e.getAddList())){
                        r.or(e.getCondition());
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
            //if(node.holds(va.getPreconditionArray())){
            if(node.holds(va.getPreconditions())){
                retList.add(va);
                //System.out.println(va.getName());
            }

        }
        return retList;
    }
}
