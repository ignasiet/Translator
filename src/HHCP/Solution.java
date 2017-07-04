package HHCP;

import org.jgrapht.DirectedGraph;
import org.jgrapht.ext.DOTExporter;
import org.jgrapht.ext.EdgeNameProvider;
import org.jgrapht.ext.StringEdgeNameProvider;
import org.jgrapht.ext.VertexNameProvider;
import org.jgrapht.graph.ClassBasedEdgeFactory;
import org.jgrapht.graph.DirectedMultigraph;
import causalgraph.Edge;
import causalgraph.Vertex;

import java.io.*;
import java.util.BitSet;
import java.util.HashSet;
import java.util.Stack;

/**
 * Created by ignasi on 19/05/17.
 */
public class Solution {
    private DirectedMultigraph<String, Edge> graph;
    private int numberNodes = 0;

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
            if(s.holds(problem.getGoal())){
                from = cleanStringDot(s.parentAction);
                graph.addVertex("Goal");
                addEdge(from, "Goal", "");
                continue;
            }
            String label = "";
            if(s.parentAction != null){
            	if(problem.getAction(s.indexAction).isNondeterministic){
                	label = problem.getPredicate(problem.getAction(s.indexAction).getEffects().get(s.indexEffect).getAddList().nextSetBit(0));
                }
                from = cleanStringDot(s.parentAction);
            }
            int act = -1;
            /*if(policyP.action(s.getState()) == -1){
            	System.out.println("WTF??");
            	System.out.println(problem.printState(s.getState()));
            	exportGraph();
            	return;
            }else{
            	act = policyP.action(s.getState());
            }*/
            act = policyP.action(s.getState());
            VAction a = problem.getAction(act);
            to = cleanStringDot(a.getName());
            graph.addVertex(from);
            graph.addVertex(to);
            //if(from.equals(to)) continue;
            if(graph.getEdge(from, to) != null) continue;
            addEdge(from, to, label);
            if(a.isNondeterministic){
                for(Node succ : s.applyNonDeterministicAction(a, problem.vAxioms)){
                    open.push(succ);
                }
            }else{
                Node succ = s.applyDeterministicAction(a);
                open.push(succ);
            }
            solved.add(s.getState());
        }
        System.out.println("Graph created.");
        System.out.println("Policy size: " + solved.size());
        exportGraph();
    }
    
    private void updateEdge(String from, String to, String label){
    	Edge<String> edge = new Edge<String>(from, to, label);
    	graph.removeEdge(edge);
    	graph.addEdge(from, to, edge);
    }

    private void addEdge(String from, String to, String label){
        Edge<String> edge = new Edge<String>(from, to, label);
        numberNodes++;
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
        VertexNameProvider<String> p1 = new Vertex();
        EdgeNameProvider<Edge> edgeLabel = new StringEdgeNameProvider<Edge>();
        DOTExporter<String, Edge> exporter = new DOTExporter<String, Edge>(p1, p2, edgeLabel);
        exporter.export(new OutputStreamWriter(out), graph2);
    }

    private String cleanStringDot(String s){
        s = s.replace("-", "");
        return s;
    }

    private void exportGraph() {
        // note directed edges are printed as: (<v1>,<v2>)
        //System.out.println(graph.toString());
        System.out.println("Nodes: " + numberNodes);
        File file = new File("./plan.dot");
        try {
            toDot(new FileOutputStream(file), graph);
            System.out.println("Dot file saved in plan.dot.\n Using graphviz: dot -Tpdf plan.dot -o plan.pdf");
        } catch (FileNotFoundException e1) {
            e1.printStackTrace();
        }
    }
}
