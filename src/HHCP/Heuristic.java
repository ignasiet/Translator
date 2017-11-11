package HHCP;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;

/**
 * Created by ignasi on 15/05/17.
 */
public class Heuristic {

    Problem problem;
    private HashSet<Integer> landmarks;
    private RelaxedGraphH rp;
    private String heuristic = "";
    private JustificationGraph justGraph;
    private PartialPolicy policy;
    private HashMap<BitSet, Float> values;
    private HashSet<BitSet> solved;

    public Heuristic(Problem p, ArrayList<Integer> l, JustificationGraph jG, String h){
        problem = p;
        heuristic = h;
        justGraph = jG;
        if(l != null) landmarks = new HashSet<Integer>(l);
        rp = new RelaxedGraphH(problem);
    }

    public long getValue(Node node){
        rp.solutionCost = 0;
        if(heuristic.equals("ff")) {
            HashSet<Integer> landmarksNotReached;
            if (landmarks != null) {
                landmarksNotReached = new HashSet<>(landmarks);
                for (Integer i : landmarks) {
                    if (node.getState().get(i)) {
                        landmarksNotReached.remove(i);
                    }
                }
                rp.calculateHeuristic(node.getState(), landmarks);
                return returnValue(rp, node);
            } else {
                rp.calculateHeuristic(node.getState(), null);
                return returnValue(rp, node);
            }
        }else{
            return landmarkCutH.getHMax(node.getState(), justGraph, problem.getGoal());
        }
    }

    public long getValue(fNode node){
        rp.solutionCost = 0;
        if(heuristic.equals("ff")) {
            HashSet<Integer> landmarksNotReached;
            if (landmarks != null) {
                landmarksNotReached = new HashSet<>(landmarks);
                for (Integer i : landmarks) {
                    if (node.getState().get(i)) {
                        landmarksNotReached.remove(i);
                    }
                }
                rp.calculateHeuristic(node.getState(), landmarks);

                return returnValue(rp, node);
            } else {
                rp.calculateHeuristic(node.getState(), null);
                return returnValue(rp, node);
            }
        }else{
            return landmarkCutH.getHMax(node.getState(), justGraph, problem.getGoal());
        }
    }

    public long getValueI(Node node, BitSet acts){
        rp = new RelaxedGraphH(problem);
        rp.preScheduleActions(acts);
        rp.calculateHeuristic(node.getState(), null);
        return returnValue(rp, node);
    }

    public void updateValue(int index, int value){
        rp.updateCost(index, value);
    }

    private long returnValue(RelaxedGraphH rp, Node node){
        try {
            if (rp.getValue() != 0 && rp.getValue() < Long.MAX_VALUE) {
                node.setRelaxedSolution(rp.getRelaxedSolution());
                //node.setBestRelaxedAction(problem.getAction(extractPreferredAction(rp.reSolution)).getName());
                node.setBestRelaxedAction(problem.getAction(rp.getRelaxedSolution().get(rp.getRelaxedSolution().size() - 1)).getName());
            }
            return rp.getValue();
        }catch (Exception e){
            System.out.println("Error: ");
            e.printStackTrace();
            System.exit(0);
            return -1;
        }
    }

    private long returnValue(RelaxedGraphH rp, fNode node){
        try {
            if (rp.getValue() != 0 && rp.getValue() < Long.MAX_VALUE) {
                node.setRelaxedSolution(rp.getRelaxedSolution());
                //node.setBestRelaxedAction(problem.getAction(extractPreferredAction(rp.reSolution)).getName());
                node.setBestRelaxedAction(problem.getAction(rp.getRelaxedSolution().get(rp.getRelaxedSolution().size() - 1)).getName());
            }
            return rp.getValue();
        }catch (Exception e){
            System.out.println("Error: ");
            e.printStackTrace();
            System.exit(0);
            return -1;
        }
    }

    /**Need to order the best first actions*/
    public Integer extractPreferredAction(HashMap<Integer, ArrayList<Integer>> reSolution) {
        ArrayList<Integer> l = reSolution.get(1);
        if(l.size()>1){
            for(Integer i : l){
                if(problem.getAction(i).isObservation) return i;
            }
            return l.get(0);
        }else{
            return l.get(0);
        }
    }

    public String getExcuse() {
        return problem.getAction(rp.getRelaxedSolution().get(rp.getRelaxedSolution().size() - 1)).getName();
    }

    public void useCosts(int[] costsVector) {
        rp.setCost(costsVector);
    }
}
