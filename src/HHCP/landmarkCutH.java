package HHCP;

import causalgraph.Edge;
import org.jgrapht.alg.KShortestPaths;

import java.util.BitSet;
import java.util.HashSet;
import java.util.Set;

/**
 * Created by ignasi on 22/08/17.
 */
public class landmarkCutH {

    private Problem problem;
    private JustificationGraph jG;
    private static BitSet level = new BitSet();

    public static int getHMax(BitSet state, JustificationGraph j, BitSet goal){
        boolean reached = false;
        BitSet goalLevel = (BitSet) goal.clone();
        BitSet currentLevel = new BitSet();
        BitSet reachedPredicates = new BitSet();
        double cost = 0;
        while(!reached){
            if(goalLevel.equals(currentLevel)) reached = true;
            currentLevel = (BitSet) goalLevel.clone();
            cost += getNewLevel(currentLevel, reachedPredicates, j);
            reachedPredicates.or(currentLevel);
            goalLevel.or(level);
        }
        level.clear();
        return (int)cost;
    }

    private static double getNewLevel(BitSet goal, BitSet reached, JustificationGraph jG){
        double min = Integer.MAX_VALUE;
        for(int i = goal.nextSetBit(0); i>= 0; i = goal.nextSetBit(i+1)) {
            Set<Edge> hS = jG.getIncomingEdgesOf(String.valueOf(i));
            for (Edge e : hS) {
                if(!jG.relevants.get(Integer.parseInt(e.getSource()))) continue;
                if (reached.get(Integer.parseInt(e.getSource()))) continue;
                level.set(Integer.parseInt(e.getSource()));
                if (jG.getEdgeWeight(e) < min) min = jG.getEdgeWeight(e);
            }
        }
        return min;
    }
}
