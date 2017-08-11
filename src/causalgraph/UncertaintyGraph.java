package causalgraph;

import org.jgrapht.DirectedGraph;
import org.jgrapht.ext.DOTExporter;
import org.jgrapht.ext.VertexNameProvider;
import org.jgrapht.graph.ClassBasedEdgeFactory;
import org.jgrapht.graph.DirectedMultigraph;
import pddlElements.Domain;

import java.io.*;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

/**
 * Created by ignasi on 06/07/17.
 */
public class UncertaintyGraph {

    private DirectedMultigraph<String, Edge> graph;
    private Set<String> observables = new HashSet<String>();
    private Integer index = 0;
    private Set<String> literals = new HashSet<String>();
    private Hashtable<String, Integer> predicateCount;

    public UncertaintyGraph(Domain d){
        graph = createStringGraph();
        for(String key : d.relevanceSet.keySet()){
            ArrayList<ArrayList<String>> lists = new ArrayList<>(d.relevanceSet.get(key));
            for(String predicate : lists.get(0)){
                addEdge(predicate, key);
                if(!d.ruleSet.containsKey(predicate.replace("~", ""))) continue;
                for(ArrayList<String> relevants : d.ruleSet.get(predicate.replace("~", ""))){
                    addEdge("axiom-"+predicate+index, predicate);
                    for(String rel : relevants){
                        addEdge(rel, "axiom-"+predicate+index);
                    }
                    index++;
                }
            }
        }
        exportGraph();
    }

    private void addEdge(String from, String to){
        graph.addVertex(cleanStringDot(from));
        graph.addVertex(cleanStringDot(to));
        Edge<String> edge = new Edge<String>(cleanStringDot(from), cleanStringDot(to), "");
        graph.addEdge(cleanStringDot(from), cleanStringDot(to), edge);
    }

    private void exportGraph() {
        File file = new File("./Uncertainty.dot");
        try {
            toDot(new FileOutputStream(file), graph);
            System.out.println("Dot file saved in Graph.dot.\n Using graphviz: dot -Tpdf Graph.dot -o Graph.pdf");
        } catch (FileNotFoundException e1) {
            e1.printStackTrace();
        }
    }

    public static void toDot(OutputStream out, DirectedGraph<String, Edge> graph2) {
        //VertexNameProvider<String> provider = new ActionNameProvider();
        VertexNameProvider<String> p2 = new Vertex();
        DOTExporter<String, Edge> exporter = new DOTExporter<String, Edge>(p2, null, null);
        exporter.export(new OutputStreamWriter(out), graph2);
    }

    private DirectedMultigraph<String, Edge> createStringGraph(){
        DirectedMultigraph<String, Edge> g = new DirectedMultigraph<String, Edge>(
                new ClassBasedEdgeFactory<String, Edge>(Edge.class));
        return g;
    }

    private String cleanStringDot(String s){
        s = s.replace("~", "not_");
        return s.replace("-", "wtz");
    }

    private String cleanBackDot(String s){
        s = s.replace("not_", "~");
        s = s.replace("wtz", "-");
        return s;
    }
}
