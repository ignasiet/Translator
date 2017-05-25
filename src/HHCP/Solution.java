package HHCP;

import org.jgrapht.DirectedGraph;
import org.jgrapht.ext.DOTExporter;
import org.jgrapht.ext.VertexNameProvider;
import org.jgrapht.graph.ClassBasedEdgeFactory;
import org.jgrapht.graph.DirectedMultigraph;
import trapper.Edge;
import trapper.Vertex;

import java.io.*;
import java.util.BitSet;
import java.util.HashSet;
import java.util.Stack;

/**
 * Created by ignasi on 19/05/17.
 */
public class Solution {
    private DirectedMultigraph<String, Edge> graph;

    public Solution(PartialPolicy policyP, BitSet initState, Problem problem) {
        graph = createStringGraph();
        Node n = new Node(initState);
        Stack<Node> open = new Stack<Node>();
        open.push(n);
        String from = "root";
        String to = "";
        HashSet<BitSet> solved = new HashSet<BitSet>();
        while(!open.isEmpty()){
            Node s = open.pop();
            /*if(solved.contains(s.getState())){
                continue;
            }*/
            if(s.holds(problem.getGoal())){
                from = cleanStringDot(s.parentAction);
                graph.addVertex("Goal");
                addEdge(from, "Goal", "");
                continue;
            }
            if(s.parentAction != null){
                from = cleanStringDot(s.parentAction);
            }
            VAction a = problem.getAction(policyP.action(s.getState()));
            to = cleanStringDot(a.getName());
            graph.addVertex(from);
            graph.addVertex(to);
            if(from.equals(to)) continue;
            addEdge(from, to, "");
            if(a.isNondeterministic){
                for(Node succ : s.applyNonDeterministicAction(a)){
                    open.push(succ);
                }
            }else{
                Node succ = s.applyDeterministicAction(a);
                open.push(succ);
            }
            solved.add(s.getState());
        }
        System.out.println("Graph created.");
        exportGraph();
    }

    private void addEdge(String from, String to, String label){
        Edge<String> edge = new Edge<String>(from, to, label);
        graph.addEdge(from, to, edge);
    }

    private DirectedMultigraph<String, Edge> createStringGraph(){
        DirectedMultigraph<String, Edge> g = new DirectedMultigraph<String, Edge>(
                new ClassBasedEdgeFactory<String, Edge>(Edge.class));
        return g;
    }

    public static void toDot(OutputStream out, DirectedGraph<String, Edge> graph2) {
        //VertexNameProvider<String> provider = new ActionNameProvider();
        VertexNameProvider<String> p2 = new Vertex();
        DOTExporter<String, Edge> exporter = new DOTExporter<String, Edge>(p2, null, null);
        exporter.export(new OutputStreamWriter(out), graph2);
    }

    private String cleanStringDot(String s){
        s = s.replace("-", "");
        return s;
    }

    private void exportGraph() {
        // note directed edges are printed as: (<v1>,<v2>)
        //System.out.println(graph.toString());
        File file = new File("./plan.dot");
        try {
            toDot(new FileOutputStream(file), graph);
            System.out.println("Dot file saved in Graph.dot.\n Using graphviz: dot -Tpdf plan.dot -o plan.pdf");
        } catch (FileNotFoundException e1) {
            e1.printStackTrace();
        }
    }
}
