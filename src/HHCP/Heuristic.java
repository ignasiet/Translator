package HHCP;

import java.util.BitSet;

/**
 * Created by ignasi on 15/05/17.
 */
public class Heuristic {

    Problem problem;
    public Heuristic(Problem p){
        problem = p;
    }

    public int getValue(Node node){
        RelaxedGraphH rp = new RelaxedGraphH(problem, node.getState());
        if(rp.getValue() != 0){
            node.setRelaxedSolution(rp.getRelaxedSolution());
            node.setBestRelaxedAction(problem.getAction(rp.getRelaxedSolution().get(rp.getRelaxedSolution().size()-1)).getName());

        }
        return rp.getValue();
    }


}
