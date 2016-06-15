package planner;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import pddlElements.Action;
import pddlElements.Axiom;
import pddlElements.Domain;
import pddlElements.Effect;

import org.jgrapht.DirectedGraph;
import org.jgrapht.UndirectedGraph;
import org.jgrapht.ext.DOTExporter;
import org.jgrapht.ext.VertexNameProvider;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge; 

public class CausalGraph {
	public Hashtable<String, ArrayList<String>> antecessors = new Hashtable<String, ArrayList<String>>();
	public Hashtable<String, ArrayList<String>> successors = new Hashtable<String, ArrayList<String>>();
	private DirectedGraph<String, DefaultEdge> graph; 
	
	public CausalGraph(Domain d){
		Enumeration<String> e = d.list_actions.keys();
		while(e.hasMoreElements()){
			Action a = d.list_actions.get(e.nextElement().toString());
			extract(a);
		}
		e = antecessors.keys();
		while(e.hasMoreElements()){
			String key = e.nextElement().toString();
			ArrayList<String> list = (ArrayList<String>) antecessors.get(key).clone();
			construct(key, list);
		}
        extractAxioms(d);
        graph = createStringGraph();
        // note directed edges are printed as: (<v1>,<v2>)
        System.out.println(graph.toString());
        File file = new File("./Graph.dot");
    	try {
			toDot(new FileOutputStream(file), graph);
			System.out.println("Dot file saved in Graph.dot.\n dot -Tpdf Graph.dot -o Graph.pdf");
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
		}
        
	}
	
	private DirectedGraph<String, DefaultEdge> createStringGraph(){
        DirectedGraph<String, DefaultEdge> g = new DefaultDirectedGraph<>(DefaultEdge.class);
        /*antecessors.keys();
		while(e.hasMoreElements()){
			String key = e.nextElement().toString();
			g.addVertex(cleanStringDot(key));
		}*/
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
		
		
        
        /*String v1 = "v1";
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
        g.addEdge(v4, v1);*/

        return g;
    }
	
	private String cleanStringDot(String s){
		s = s.replace("~", "not_");
		return s.replace("-", "");
	}
	
	public static void toDot(OutputStream out, DirectedGraph<String, DefaultEdge> graph) { 
		//VertexNameProvider<String> provider = new ActionNameProvider(); 
		VertexNameProvider<String> p2 = new Vertex();
		DOTExporter<String, DefaultEdge> exporter = new DOTExporter<String, DefaultEdge>(p2, null, null); 
		exporter.export(new OutputStreamWriter(out), graph); 
	} 

    private void extractAxioms(Domain d){
        for(Axiom ax : d._Axioms){
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
        }
    }

    private void construct(Domain d){
        for(Axiom ax : d._Axioms){
            for(String p : ax._Head){

            }
        }
    }

	private void extract(Action a) {
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
	}
	
	public boolean isPossibleDeadEnd(Effect e){
		if(e._Condition.isEmpty()){
			return false;
		}
		for(String effect : e._Effects){
			if(effect.startsWith("~")){
				if(successors.containsKey(effect.substring(1)) && !successors.containsKey(effect) 
						&& antecessors.containsKey(effect) && !antecessors.containsKey(effect.substring(1))){
					return true;
				}
			}
		}
		return false;
	}
}