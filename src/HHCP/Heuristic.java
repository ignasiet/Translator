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

    public int getValue(BitSet state, VAction a){
        RelaxedGraphH rp = new RelaxedGraphH(problem, state);
        return rp.getValue();
    }


}
