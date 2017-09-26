package HHCP;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;

/**
 * Created by ignasi on 12/09/17.
 */
public class searchHelper {

    public static boolean entails(BitSet s, BitSet goal) {
        BitSet A = (BitSet) goal.clone();
        A.and(s);
        return A.equals(goal);
    }

    public static ArrayList<VAction> getApplicableActions(Node node){
        ArrayList<VAction> retList = new ArrayList<VAction>();
        return retList;
    }

    public static Node initLayers(Node state, Problem p) {
        if(state.parent != null) {
            //state.parent.greedyAction = state.indexAction;
        }
        Node n = new Node((BitSet) state.getState().clone());
        //1 Init list of scheduled actions: no action scheduled
        n.parent = state.parent;
        n.parentAction = state.parentAction;
        n.indexAction = state.indexAction;
        if(state.visited == null){
            n.visited = new HashSet<BitSet>();
        }else {
            n.addVisited(state.visited);
        }
        n.visited.add(state.getState());
        n.setActionCounter(new int[p.getVaList().size()]);
        n.setActionLayer(new int[p.getVaList().size()]);
        n.setFacts(new int[p.getSize()]);
        BitSet scheduledActions = new BitSet();
        n.setCost(state.getCost());
        n.setHeuristic(state.getH());
        //scheduledActions = new BitSet(problem.getVaList().size());
        //2 For every predicate that is in the current state, update facts layer to put a 0 value
        for (int i = state.getState().nextSetBit(0); i >= 0; i = state.getState().nextSetBit(i+1)) {
            //System.out.println("Predicate: " + i + " correspond to: " + problem.getPredicate(i));
            n.getFactslayer()[i] = 1;
            //3 Update actions whose preconditions have been updated
            n.updateActionCounter(i, p, n, scheduledActions);
        }
        n.setScheduledActions(scheduledActions);
        return n;
    }

    public static void updateHeuristic(Node child, Node father, VAction va, Heuristic h) {
        child.setCost(father.getCost() + va.cost);
        long heuristic = h.getValue(child);
        //if(va.isNondeterministic) heuristic += 1;
        child.setHeuristic(heuristic);
    }

    public static void updateCost(Node child, Node father, VAction va, long cost) {
        child.setCost(father.getCost() + va.cost);
        child.setHeuristic(cost);
        child.value = cost;
    }

    public static void printPolicy(BitSet initState, PartialPolicy policyP, Problem problem) {
        Solution s = new Solution(policyP, initState, problem);
    }

    public static void printStats(PartialPolicy policyP, double startTime, double endTime, Problem p){
        System.out.println("==========================================================");
        System.out.println("Initial state solved " + policyP.valid(p.getInitState()));
        System.out.println("Results:");
        System.out.println("Planner time: " + (endTime - startTime) + " Milliseconds");
        System.out.println("Number of nodes: " + policyP.partial.size());
        System.out.println("Policy size: " + policyP.size());
        System.out.println("Number of states solved: " + policyP.marked.size());
    }

}
