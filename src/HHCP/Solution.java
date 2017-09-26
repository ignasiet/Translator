package HHCP;

import causalgraph.*;
import org.jgrapht.DirectedGraph;
import org.jgrapht.ext.DOTExporter;
import org.jgrapht.ext.EdgeNameProvider;
import org.jgrapht.ext.StringEdgeNameProvider;
import org.jgrapht.ext.VertexNameProvider;
import org.jgrapht.graph.ClassBasedEdgeFactory;
import org.jgrapht.graph.DirectedMultigraph;

import java.io.*;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Stack;

/**
 * Created by ignasi on 19/05/17.
 */
public class Solution {
    private DirectedMultigraph<VertexNode, Edge> graph;
    private HashMap<BitSet, Integer> idStates = new HashMap<>();
    private HashSet<BitSet> visitedStates = new HashSet<BitSet>();
    private HashSet<BitSet> deadEnds = new HashSet<BitSet>();
    private int numberDeadEnds = 0;
    private int numberNodes = 0;
    private int i = 2;

    public Solution(PartialPolicy policyP, BitSet initState, Problem problem) {
        graph = createStringGraph();
        Node n = new Node(initState);
        String lastDivisor = "";
        int[] factlayer = problem.initLayers(initState);
        n.setActionCounterInc(problem);
        n.setActionLayer(new int[problem.getVaList().size()]);
        n.setFacts(factlayer);
        Stack<Node> open = new Stack<Node>();
        open.push(n);
        addVertex("root", 0);
        addVertex("Goal", 1);

        addNewState(n.getState());
        HashSet<BitSet> solved = new HashSet<BitSet>();

        while(!open.isEmpty()){
            Node s = open.pop();
            visitedStates.add(s.getState());
            if(s.holds(problem.getGoal())){
                VertexNode goalNode = getVertex("Goal");
                VertexNode origin = getVertex(cleanStringDot(s.parentAction));
                addEdge(origin, goalNode, "");
                continue;
            }
            //if(idStates.containsKey(s.getState())) continue;

            String label = "";
            VertexNode origin;
            if(s.parentAction == null){
                origin = getVertex("root");
            }else{
                if(problem.getAction(s.indexAction).isNondeterministic){
                    label = problem.getPredicate(problem.getAction(s.indexAction)
                            .getEffects().get(s.indexEffect).getAddList().nextSetBit(0));
                }
                origin = addVertex(cleanStringDot(s.parentAction), idStates.get(s.parent.getState()));
                i++;
            }

            int act = policyP.action(s.getState());
            if(act == -1){
                VertexNode destiny = addVertex("DEAD-END!", idStates.get(s.getState()));
                addEdge(origin, destiny, label);
                deadEnds.add(s.getState());
                numberDeadEnds++;
            }else{
                VAction a = problem.getAction(act);
                VertexNode destiny = addVertex(cleanStringDot(a.getName()), idStates.get(s.getState()));
                if(origin.getId() == destiny.getId()){
                    continue;
                }
                addEdge(origin, destiny, label);
                if(a.isNondeterministic){
                    for(Node succ : s.applyNonDeterministicAction(a, problem)){
                        if(!visitedStates.contains(succ.getState())) open.push(succ);
                        addNewState(succ.getState());
                    }
                }else{
                    Node succ = s.applyDeterministicAction(a, problem);
                    if(!visitedStates.contains(succ.getState())) open.push(succ);
                    addNewState(succ.getState());
                }
                solved.add(s.getState());
            }

            //origin = getVertex(cleanStringDot(s.parentAction));
            //VertexNode destiny = addVertex(cleanStringDot(a.getName()), idStates.get(s.getState()));
            //if(from.equals(to)) continue;
            //if(!(graph.getEdge(from, to) != null))
            //addEdge(origin, destiny, label);



        }
        System.out.println("Graph created.");
        System.out.println("Size of the solution: " + visitedStates.size());
        System.out.println("Number of dead ends: " + numberDeadEnds);
        exportGraph();
    }

    private void addNewState(BitSet state){
        idStates.put(state, i);
        i++;
    }

    private VertexNode getVertex(String vertex){
        for(VertexNode v : graph.vertexSet()){
            if(v.getLabel().equals(vertex)){
                return v;
            }
        }
        return null;
    }

    private VertexNode getVertex(int vertex){
        for(VertexNode v : graph.vertexSet()){
            if(v.getId() == vertex){
                return v;
            }
        }
        return null;
    }

    private void addEdge(VertexNode from, VertexNode to, String label){
        Edge<VertexNode> edge = new Edge<VertexNode>(from, to, label);
        if(!graph.containsEdge(edge)) graph.addEdge(from, to, edge);
        numberNodes++;
    }

    private VertexNode addVertex(String vertex, int i){
        VertexNode v = new VertexNode(vertex, i);
        /*if(!graph.containsVertex(v)){

        }*/
        graph.addVertex(v);
        return v;
    }

    private DirectedMultigraph<VertexNode, Edge> createStringGraph(){
        DirectedMultigraph<VertexNode, Edge> g = new DirectedMultigraph<VertexNode, Edge>(
                new ClassBasedEdgeFactory<VertexNode, Edge>(Edge.class));
        return g;
    }

    public static void toDot(OutputStream out, DirectedGraph<VertexNode, Edge> graph2) {
        //VertexNameProvider<String> provider = new ActionNameProvider();
        VertexNameProvider<VertexNode> p2 = new VertexNodeProvider();
        VertexNameProvider<VertexNode> p1 = new VertexNodeId();
        EdgeNameProvider<Edge> edgeLabel = new StringEdgeNameProvider<Edge>();
        DOTExporter<VertexNode, Edge> exporter = new DOTExporter<VertexNode, Edge>(p1, p2, edgeLabel);
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
        File file = new File("./solution.dot");
        try {
            toDot(new FileOutputStream(file), graph);
            System.out.println("Dot file saved in solution.dot.\n Using graphviz: dot -Tpdf solution.dot -o plan.pdf");
        } catch (FileNotFoundException e1) {
            e1.printStackTrace();
        }
    }
}
