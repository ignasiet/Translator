package HHCP;

import java.util.ArrayList;
import java.util.BitSet;

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

    public static Node initLayers(BitSet state, Problem p) {
        Node n = new Node(state);
        //1 Init list of scheduled actions: no action scheduled
        n.setActionCounter(new int[p.getVaList().size()]);
        n.setActionLayer(new int[p.getVaList().size()]);
        n.setFacts(new int[p.getSize()]);
        BitSet scheduledActions = new BitSet();
        //scheduledActions = new BitSet(problem.getVaList().size());
        //2 For every predicate that is in the current state, update facts layer to put a 0 value
        for (int i = state.nextSetBit(0); i >= 0; i = state.nextSetBit(i+1)) {
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
        child.setHeuristic(h.getValue(child));
    }

}
