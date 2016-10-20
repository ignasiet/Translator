package trapper;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.jgrapht.DirectedGraph;
import org.jgrapht.Graphs;
import org.jgrapht.ext.DOTExporter;
import org.jgrapht.ext.VertexNameProvider;
import org.jgrapht.graph.ClassBasedEdgeFactory;
import org.jgrapht.graph.DirectedMultigraph;

import parser.ParserHelper;
import pddlElements.Action;
import pddlElements.Axiom;
import pddlElements.Disjunction;
import pddlElements.Domain;
import pddlElements.Effect;
import trapper.Edge;

public class CausalGraph {
	private DirectedMultigraph<String, Edge> graph;
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
				feedObservableLiterals(a);
				continue;
			}
			buildgraph(d,a);
		}
		checkliterals();
		extractDisjunctions(d);
        extractAxioms(d);
        exportGraph();
	}
	
	protected DirectedMultigraph<String, Edge> getGraph(){
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
    				Edge<String> edge = new Edge<String>(pred, ParserHelper.complement(pred2), "Disjunction");
    				graph.addVertex(pred);
    				graph.addVertex(ParserHelper.complement(pred2));
    				graph.addEdge(pred, ParserHelper.complement(pred2), edge);
    				edge = new Edge<String>(ParserHelper.complement(pred), pred2, "Disjunction");
    				graph.addVertex(ParserHelper.complement(pred));
    				graph.addVertex(pred2);
    				graph.addEdge(ParserHelper.complement(pred), pred2, edge);
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
        /*System.out.println(graph.toString());
        File file = new File("./Graph.dot");
    	try {
			toDot(new FileOutputStream(file), graph);
			System.out.println("Dot file saved in Graph.dot.\n Using graphviz: dot -Tpdf Graph.dot -o Graph.pdf");
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
		}*/
		
		try{
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
		}
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
	
	/*private DirectedGraph<String, DefaultEdge> createStringGraph(){
        DirectedGraph<String, DefaultEdge> g = new DefaultDirectedGraph<>(DefaultEdge.class);
        antecessors.keys();
		while(e.hasMoreElements()){
			String key = e.nextElement().toString();
			g.addVertex(cleanStringDot(key));
		}
        Enumeration<String> e = antecessors.keys();
		while(e.hasMoreElements()){
			String to = e.nextElement().toString();
			g.addVertex(cleanStringDot(to));
			ArrayList<String> origins = antecessors.get(to);
			for(String from : origins){
				g.addVertex(cleanStringDot(from));
				g.addEdge(cleanStringDot(from), cleanStringDot(to));
			}
		}        
        String v1 = "v1";
        String v2 = "v2";
        String v3 = "v3";
        String v4 = "v4";

        // add the vertices
        g.addVertex(v1);
        g.addVertex(v2);
        g.addVertex(v3);
        g.addVertex(v4);

        // add edges to create a circuit
        g.addEdge(v1, v2);
        g.addEdge(v2, v3);
        g.addEdge(v3, v4);
        g.addEdge(v4, v1);

        return g;
    }*/
	
	@SuppressWarnings("rawtypes")
	private DirectedMultigraph<String, Edge> createStringGraph(){
		DirectedMultigraph<String, Edge> g = new DirectedMultigraph<String, Edge>(
	                    new ClassBasedEdgeFactory<String, Edge>(Edge.class));
		return g;		
    }
	
	private void buildgraph(Domain d, Action a) {
		for(Effect e : a._Effects){
			for(String to : e._Effects){
				/*if(isVariable(to)){
					addToVariablesList(variables, to);
				}*/
				//if(!d.isUncertain(to)) continue;
				graph.addVertex(to);
				ArrayList<String> origins = new ArrayList<String>(e._Condition);
				origins.addAll(a._precond);
				for(String from : origins){
					Edge<String> edge = new Edge<String>(from, to, a.Name);
					graph.addVertex(from);
					if(from.equals(to)){
						//System.out.println("Loop: action " + a.Name + " " + from + " " + to);
						continue;
					}
					graph.addEdge(from, to, edge);
				}
			}
		}
	}
		
	private String cleanStringDot(String s){
		s = s.replace("~", "not_");
		return s.replace("-", "");
	}
	
	public static void toDot(OutputStream out, DirectedGraph<String, Edge> graph2) { 
		//VertexNameProvider<String> provider = new ActionNameProvider(); 
		VertexNameProvider<String> p2 = new Vertex();
		DOTExporter<String, Edge> exporter = new DOTExporter<String, Edge>(p2, null, null);
		exporter.export(new OutputStreamWriter(out), graph2); 
	}
	
	private void feedObservableLiterals(Action a) {
		for(Effect effect : a._Effects){
			for(String observable : effect._Effects){
				observables.add(observable);
				graph.addVertex(observable);
				graph.addVertex(ParserHelper.complement(observable));
				for(String precondition : a._precond){
					graph.addVertex(precondition);
					Edge<String> edge = new Edge<String>(precondition, observable, a.Name);
					graph.addEdge(precondition, observable, edge);
					Edge<String> edgeComplement = new Edge<String>(precondition, ParserHelper.complement(observable), a.Name);
					graph.addEdge(precondition, ParserHelper.complement(observable), edgeComplement);
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
    				Edge<String> edge = new Edge<String>(from, to, ax._Name);
    				graph.addVertex(from);
    				graph.addVertex(to);
    				graph.addEdge(from, to, edge);
    			}				
    		}
    	}
    }

    /*private void extract(Action a) {
		for(Effect e : a._Effects){
			for(String effect : e._Effects){
				ArrayList<String> list = new ArrayList<String>(a._precond);
				list.addAll(e._Condition);
				if(antecessors.containsKey(effect)){
					//list.addAll(antecessor.get(effect));
					//Remove duplicates
					Set<String> hs = new HashSet<>();
					hs.addAll(list);
					hs.addAll(antecessors.get(effect));
					list.clear();
					list.addAll(hs);
					antecessors.put(effect, list);
				}else{
					antecessors.put(effect, list);
				}
			}
		}
	}
	
	private void construct(String key, ArrayList<String> list){
		for(String s : list){
			if(successors.containsKey(s)){
				//Remove duplicates
				Set<String> hs = new HashSet<>();
				hs.addAll(successors.get(s));
				ArrayList<String> sucList = new ArrayList<String>();
				hs.add(key);
				sucList.addAll(hs);
				successors.put(s, sucList);
			}else{
				ArrayList<String> sucList = new ArrayList<String>();
				sucList.add(key);
				successors.put(s, sucList);
			}
		}
	}*/
    
    public ArrayList<String> enhancedObservation(String observed){
    	List<String> causal = Graphs.predecessorListOf(graph, observed);
    	List<String> inversed = Graphs.predecessorListOf(graph, ParserHelper.complement(observed));
    	inversed.removeAll(causal);
    	ArrayList<String> l = new ArrayList<String>();
    	if(inversed.size() == 1){
    		l.add(ParserHelper.complement(inversed.get(0)));
    		return l;
    	}
    	for(String obs : inversed){
    		if(obs.startsWith("~")) continue;
    		l.add(ParserHelper.complement(obs));
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