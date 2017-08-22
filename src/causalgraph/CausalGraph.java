package causalgraph;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import org.jgrapht.DirectedGraph;
import org.jgrapht.Graphs;
import org.jgrapht.alg.DijkstraShortestPath;
import org.jgrapht.ext.DOTExporter;
import org.jgrapht.ext.VertexNameProvider;
import org.jgrapht.graph.ClassBasedEdgeFactory;
import org.jgrapht.graph.DefaultDirectedWeightedGraph;
import org.jgrapht.graph.DirectedMultigraph;

import org.jgrapht.graph.DirectedWeightedMultigraph;
import parser.ParserHelper;
import pddlElements.Action;
import pddlElements.Axiom;
import pddlElements.Disjunction;
import pddlElements.Domain;
import pddlElements.Effect;

public class CausalGraph {
	private DefaultDirectedWeightedGraph<String, Edge> graph;
	private Set<String> observables = new HashSet<String>();
	private Integer index = 0;
	private Set<String> literals = new HashSet<String>();
	private Hashtable<String, Integer> predicateCount;

	
	public CausalGraph(Domain d){
		graph = createStringGraph();
		predicateCount = new Hashtable<String, Integer>(d.count);
		Enumeration<String> e = d.list_actions.keys();
		while(e.hasMoreElements()){
			Action a = d.list_actions.get(e.nextElement().toString());
			feedLiterals(a);
			if(a.IsObservation){
				feedObservations(a);
			}else if(a._IsNondeterministic){
				feedNonDetActions(a);
			}else {
				feedActions(a);
			}
		}
		checkliterals();
		extractDisjunctions(d);
        extractAxioms(d);
        exportGraph();
	}
	
	protected DefaultDirectedWeightedGraph<String, Edge> getGraph(){
		return graph;
	}
	
	protected Set<Edge> getOutgoingEdges(String node){
		return graph.outgoingEdgesOf(node);
	}
	
	protected Set<Edge> getIncomingEdges(String node){
		return graph.incomingEdgesOf(node);
	}
	
	protected Set<Edge> getOutgoingEdges(ArrayList<String> nodes){
		Set<Edge> edges = new HashSet<Edge>();
		for(String node : nodes){
			Set<Edge> auxEdges = getOutgoingEdges(node);
			if(!edges.isEmpty()) edges.retainAll(auxEdges);
		}
		return edges;
	}
	
	private void checkliterals() {
		Set<String> newL = new HashSet<String>();
		Iterator<String> e = literals.iterator();
		while(e.hasNext()){
			String l = e.next();
			newL.add(l);
			newL.add(ParserHelper.complement(l));
		}
		literals = newL;
	}

	public Set<String> getPredecessors(String vertex){
		Set<Edge> edges = graph.incomingEdgesOf(cleanStringDot(vertex));
		HashSet<String> predecessors = new HashSet<String>();
		for(Edge<String> e : edges){
			predecessors.add(cleanBackDot(e.getV1()));
		}
		return predecessors;
	}

	public boolean isVariable(String literal){
		if(!literal.contains("_")) return false;
		String s = literal.substring(0, literal.indexOf("_")).replace("~", "");
		if(predicateCount.containsKey(s) && predicateCount.get(s) == 0){
			return true;
		}
		return false;
	}
	
	private void extractDisjunctions(Domain d) {
		for(Disjunction disj : d.list_disjunctions){
    		for(String pred : disj.getIterator()){
    			for(String pred2 : disj.getIterator()){
    				if(pred.equals(pred2)) continue;
    				Edge<String> edge = new Edge<String>(cleanStringDot(pred), cleanStringDot(ParserHelper.complement(pred2)), "Disjunction");
    				graph.addVertex(cleanStringDot(pred));
    				graph.addVertex(cleanStringDot(ParserHelper.complement(pred2)));
    				graph.addEdge(cleanStringDot(pred), cleanStringDot(ParserHelper.complement(pred2)), edge);
    				edge = new Edge<String>(cleanStringDot(ParserHelper.complement(pred)), cleanStringDot(pred2), "Disjunction");
    				graph.addVertex(cleanStringDot(ParserHelper.complement(pred)));
    				graph.addVertex(cleanStringDot(pred2));
    				graph.addEdge(cleanStringDot(ParserHelper.complement(pred)), cleanStringDot(pred2), edge);
    			}
    		}
    	}
	}
	
	private void feedLiterals(Action a) {
		getLiterals().addAll(a._precond);
		for(Effect e : a._Effects){
			getLiterals().addAll(e._Condition);
			getLiterals().addAll(e._Effects);
		}
	}
	
	private void exportGraph() {
		// note directed edges are printed as: (<v1>,<v2>)
        System.out.println(graph.toString());
        File file = new File("./Graph.dot");
    	try {
			toDot(new FileOutputStream(file), graph);
			System.out.println("Dot file saved in Graph.dot.\n Using graphviz: dot -Tpdf Graph.dot -o Graph.pdf");
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
		}
		
		/*try{
			File file = new File("./Graph.dot");
			// if file doesnt exists, then create it
			if (!file.exists()) {
				file.createNewFile();
			}
			FileWriter fw = new FileWriter(file.getAbsoluteFile());
			BufferedWriter bw = new BufferedWriter(fw);
			bw.write(printGraph());
			bw.close();
			//System.out.println(graph.toString());
			System.out.println("Dot file saved in Graph.dot.\n Using graphviz: dot -Tpdf Graph.dot -o Graph.pdf");
		}catch (IOException e1) {
			e1.printStackTrace();
		}*/
	}
	
	private String printGraph(){
		String contentGraph = "digraph G {\n";
		String edgesGraph = "";
		ArrayList<String> vertex = new ArrayList<String>(graph.vertexSet());
		for(String v : vertex){
			contentGraph = contentGraph.concat(cleanStringDot(v) + ";\n");
			List<String> succ = Graphs.successorListOf(graph, v);
			edgesGraph = edgesGraph.concat(cleanStringDot(v) + " -> { ");
			for(String e : succ){
				edgesGraph = edgesGraph.concat(cleanStringDot(e) + " ");
			}
			edgesGraph = edgesGraph.concat(" }; \n");
		}
		graph.edgeSet();
		return contentGraph + edgesGraph + "}";
	}
	
	@SuppressWarnings("rawtypes")
	private DefaultDirectedWeightedGraph<String, Edge> createStringGraph(){
		DefaultDirectedWeightedGraph<String, Edge> g = new DefaultDirectedWeightedGraph<String, Edge>(
	                    new ClassBasedEdgeFactory<String, Edge>(Edge.class));
		return g;
    }
	
	private void feedActions(Action a) {
		for(Effect e : a._Effects){
			for(String to : e._Effects){
				graph.addVertex(cleanStringDot(to));
				ArrayList<String> origins = new ArrayList<String>(e._Condition);
				origins.addAll(a._precond);
				for(String from : origins){
					Edge<String> edge = new Edge<String>(cleanStringDot(from), cleanStringDot(to), a.Name);
					graph.addVertex(cleanStringDot(from));
					if(from.equals(to)){
						continue;
					}
					graph.addEdge(cleanStringDot(from), cleanStringDot(to), edge);
					graph.setEdgeWeight(edge, a.cost);
				}
			}
		}
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
	
	public static void toDot(OutputStream out, DirectedGraph<String, Edge> graph2) { 
		//VertexNameProvider<String> provider = new ActionNameProvider(); 
		VertexNameProvider<String> p2 = new Vertex();
		DOTExporter<String, Edge> exporter = new DOTExporter<String, Edge>(p2, null, null);
		exporter.export(new OutputStreamWriter(out), graph2); 
	}
	
	private void feedObservations(Action a) {
		for(Effect effect : a._Effects){
			for(String observable : effect._Effects){
				observables.add(observable);
				graph.addVertex(cleanStringDot(observable));
				graph.addVertex(cleanStringDot(ParserHelper.complement(observable)));
				for(String precondition : a._precond){
					graph.addVertex(cleanStringDot(precondition));
					Edge<String> edge = new Edge<String>(cleanStringDot(precondition), cleanStringDot(observable), a.Name);
					graph.addEdge(cleanStringDot(precondition), cleanStringDot(observable), edge);
					Edge<String> edgeComplement = new Edge<String>(cleanStringDot(precondition), cleanStringDot(ParserHelper.complement(observable)), a.Name);
					graph.addEdge(cleanStringDot(precondition), cleanStringDot(ParserHelper.complement(observable)), edgeComplement);
					graph.setEdgeWeight(edge, a.cost);
					graph.setEdgeWeight(edgeComplement, a.cost);
				}
			}
		}
	}

	private void feedNonDetActions(Action a){
		for(Effect effect : a._Effects){
			for(String pred : effect._Effects){
				graph.addVertex(cleanStringDot(pred));
				for(String precondition : a._precond){
					graph.addVertex(cleanStringDot(precondition));
					Edge<String> edge = new Edge<String>(cleanStringDot(precondition), cleanStringDot(pred), a.Name);
					graph.addEdge(cleanStringDot(precondition), cleanStringDot(pred), edge);
					graph.setEdgeWeight(edge, a.cost);
				}
			}
		}
	}

    private void extractAxioms(Domain d){
    	/*Old version*/
        /*for(Axiom ax : d._Axioms){
            ArrayList<String> ant = new ArrayList<String>(ax._Body);
            for(String p : ax._Head)
            if(antecessors.containsKey(p)){
                Set<String> hs = new HashSet<>();
                hs.addAll(ant);
                hs.addAll(antecessors.get(p));
                ant.clear();
                ant.addAll(hs);
                antecessors.put(p, ant);
            }else{
                antecessors.put(p, ant);
            }
        }*/
    	/*New version*/
    	for(Axiom ax : d._Axioms){
    		ArrayList<String> ant = new ArrayList<String>(ax._Head);
    		ArrayList<String> body_list = new ArrayList<String>(ax._Body);
    		if(!(ax._Body.size()>1)){
    			String body = ax._Body.get(0);
        		//axiom.put(body, ant);
    		}else{
    			System.out.println("Axiom with two literals body: " + ax._Body.toString() + " implies: " + ax._Head.toString());
    		}
    		//axiom.put(ax._Head, ant);
    		for(String to : ax._Head){
    			for(String from : body_list){
    				Edge<String> edge = new Edge<String>(cleanStringDot(from), cleanStringDot(to), ax._Name);
    				graph.addVertex(cleanStringDot(from));
    				graph.addVertex(cleanStringDot(to));
    				graph.addEdge(cleanStringDot(from), cleanStringDot(to), edge);
    			}				
    		}
    	}
    }

	public HashSet<String> relevantLiterals(ArrayList<String> goalState){
		HashSet<String> visited = new HashSet<String>();
		//Start marking from node Dummy
		Stack<String> fringe = new Stack<String>();
		for(String goal : goalState){
			//Clean goal string (it is translated)
			if(goal.startsWith("K") || goal.startsWith("Kn_")){
				fringe.add(cleanStringDot(goal.replace("Kn_", "").replace("K", "")));
				//visited.add(cleanStringDot(goal.replace("Kn_", "").replace("K", "")));
			}else{
				fringe.add(goal);
			}
		}
		while(!fringe.isEmpty()){
			String current = cleanStringDot(fringe.pop());
			if(visited.contains(current)) continue;
			visited.add(current);
			Set<Edge> edges = graph.incomingEdgesOf(current);
			for(Edge edge : edges){
				String vertex = graph.getEdgeSource(edge);
				if(visited.contains(vertex)) continue;
				fringe.add(vertex);
			}
		}
		return cleanSetFluents(visited);
	}

	public HashSet<String> calculateCut(ArrayList<String> goalState){
		HashSet<String> visited = new HashSet<String>(goalState);
		for(String current : visited){
			Set<Edge> edges = graph.incomingEdgesOf(current);
		}
		return null;
	}

	private HashSet<String> cleanSetFluents(HashSet<String> visited){
		HashSet<String> originalRelevantFluents = new HashSet<String>();
		for(String fluent : visited){
			String flCleaned = cleanBackDot(fluent);
			originalRelevantFluents.add("K" + flCleaned);
		}
		return originalRelevantFluents;
	}

    public ArrayList<String> enhancedObservation(String observed){
    	List<String> causal = Graphs.predecessorListOf(graph, cleanStringDot(observed));
    	List<String> inversed = Graphs.predecessorListOf(graph, cleanStringDot(ParserHelper.complement(observed)));
    	inversed.removeAll(causal);
    	ArrayList<String> l = new ArrayList<String>();
    	if(inversed.size() == 1){
    		l.add(ParserHelper.complement(inversed.get(0)));
    		return l;
    	}
    	for(String obs : inversed){
    		if(obs.startsWith("~")) continue;
    		l.add(ParserHelper.complement(cleanBackDot(obs)));
    	}
    	return l;
    }
	
	public boolean isPossibleDeadEnd(Effect e){
		if(e._Condition.isEmpty()){
			return false;
		}
		for(String effect : e._Effects){
			if(effect.startsWith("~")){
				/*if(successors.containsKey(effect.substring(1)) && !successors.containsKey(effect) 
						&& antecessors.containsKey(effect) && !antecessors.containsKey(effect.substring(1))){
					return true;
				}*/
				/* Conditions tested:
				 * 1. The complement literal has sucessors.
				 * 2. The literal does not have sucessors.
				 * 3. The complement literal does not have predecessors.
				 * 4. The literal has predecessors.
				 * */
				if(!Graphs.successorListOf(graph, effect.substring(1)).isEmpty() &&
						Graphs.successorListOf(graph, effect).isEmpty() &&
						!Graphs.predecessorListOf(graph, effect.substring(1)).isEmpty() &&
						Graphs.predecessorListOf(graph, effect).isEmpty()){
					return true;
				}
				//if(graph.containsVertex(effect.substring(1)))
			}
		}
		return false;
	}
	
	public Set<String> getLiterals() {
		return literals;
	}
}