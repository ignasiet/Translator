package HHCP;

import causalgraph.Edge;
import org.jgrapht.graph.ClassBasedEdgeFactory;
import org.jgrapht.graph.DefaultDirectedWeightedGraph;
import java.util.*;

/**
 * Created by ignasi on 21/08/17.
 */
public class JustificationGraph {

    private DefaultDirectedWeightedGraph<String, Edge> graph;

    public JustificationGraph(Problem p){
        graph = createStringGraph();
        for(VAction va : p.getVaList()){
            if(va.isObservation){
                feedObservations(va);
            }else if(va.isNondeterministic){
                feedNonDetActions(va);
            }else{
                feedActions(va);
            }
        }
    }

    private void feedActions(VAction a) {
        for(VEffect e : a.getEffects()){
            for(int to = e.getAddList().nextSetBit(0);to>=0;to = e.getAddList().nextSetBit(to+1)){
                graph.addVertex(String.valueOf(to));
                BitSet origins = (BitSet) e.getCondition().clone();
                origins.or(a.getPreconditions());
                for(int from = origins.nextSetBit(0);from>=0;from = origins.nextSetBit(from+1)){
                    if(from == to) continue;
                    graph.addVertex(String.valueOf(from));
                    Edge<String> edge = new Edge<String>(String.valueOf(from), String.valueOf(to), a.getName());
                    graph.addEdge(String.valueOf(from), String.valueOf(to), edge);
                    graph.setEdgeWeight(edge, a.cost * -1);
                }
            }
        }
    }

    private void feedObservations(VAction a) {
        for(VEffect e : a.getEffects()){
            for(int to = e.getAddList().nextSetBit(0);to>=0;to = e.getAddList().nextSetBit(to+1)){
                graph.addVertex(String.valueOf(to));
                for(int from = a.getPreconditions().nextSetBit(0);from>=0;from = a.getPreconditions().nextSetBit(from+1)){
                    if(from == to) continue;
                    graph.addVertex(String.valueOf(from));
                    Edge<String> edge = new Edge<String>(String.valueOf(from), String.valueOf(to), a.getName());
                    graph.addEdge(String.valueOf(from), String.valueOf(to), edge);
                    graph.setEdgeWeight(edge, a.cost * -1);
                }
            }
        }
    }

    private void feedNonDetActions(VAction a){
        for(VEffect e : a.getEffects()){
            for(int to = e.getAddList().nextSetBit(0);to>=0;to = e.getAddList().nextSetBit(to+1)){
                graph.addVertex(String.valueOf(to));
                for(int from = a.getPreconditions().nextSetBit(0);from>=0;from = a.getPreconditions().nextSetBit(from+1)){
                    if(from == to) continue;
                    graph.addVertex(String.valueOf(from));
                    Edge<String> edge = new Edge<String>(String.valueOf(from), String.valueOf(to), a.getName());
                    graph.addEdge(String.valueOf(from), String.valueOf(to), edge);
                    graph.setEdgeWeight(edge, a.cost * -1);
                }
            }
        }
    }

    private DefaultDirectedWeightedGraph<String, Edge> createStringGraph(){
        DefaultDirectedWeightedGraph<String, Edge> g = new DefaultDirectedWeightedGraph<String, Edge>(
                new ClassBasedEdgeFactory<String, Edge>(Edge.class));
        return g;
    }

    public Set<Edge> getIncomingEdgesOf(String goal) {
        Set<Edge> hS = graph.incomingEdgesOf(goal);
        return hS;
    }

    public double getEdgeWeight(Edge e) {
        return graph.getEdgeWeight(e)*-1;
    }
}
