package HHCP;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;
import java.util.Stack;

/**
 * Created by ignasi on 11/09/17.
 */
public class LRTDP {

    private HashSet<BitSet> solved = new HashSet<BitSet>();
    private HashSet<BitSet> visited = new HashSet<BitSet>();

    public LRTDP(Problem p, Problem heuristicP, ArrayList<String> l, JustificationGraph jG, String heuristic) {
        while(!solved.contains(p.getInitState())){
            trial(p.getInitState());
        }
    }

    private void trial(BitSet initState) {
        Stack<BitSet> visited = new Stack<BitSet>();
        BitSet s = (BitSet) initState.clone();
        while(!solved.contains(s)){
            //Insert into visited
            visited.push(s);

        }

    }
}
