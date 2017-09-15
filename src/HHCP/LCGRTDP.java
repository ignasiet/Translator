package HHCP;

import java.util.*;

/**
 * Created by ignasi on 14/09/17.
 */
public class LCGRTDP {

    private HashSet<BitSet> solved = new HashSet<BitSet>();
    private PriorityQueue<Node> fringe;
    private Problem problem;

    public LCGRTDP(Problem p, Problem heuristicP, ArrayList<String> l, JustificationGraph jG, String heuristic){
        problem = p;
        while(!solved.contains(p.getInitState())){
            trial(p.getInitState());
        }
    }

    private void trial(BitSet initState){
        Comparator<Node> comparator = new NodeComparator();
        fringe = new PriorityQueue<Node>(100, comparator);
        BitSet s = (BitSet) initState.clone();
        Node initialNode = searchHelper.initLayers(new Node(s), problem);
        while(!initialNode.holds(problem.getGoal()) && !solved(initialNode.getState())){

        }
    }

    private boolean solved(BitSet state) {
        boolean b = solved.contains(state);
        return b;
    }
}
