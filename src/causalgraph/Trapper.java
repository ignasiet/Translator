/**
 * 
 */
package causalgraph;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import org.apache.commons.math3.util.Combinations;
import org.jgrapht.Graphs;
import org.jgrapht.graph.ClassBasedEdgeFactory;
import org.jgrapht.graph.DefaultDirectedWeightedGraph;
import org.jgrapht.graph.DirectedMultigraph;

import parser.ParserHelper;
import pddlElements.Action;
import pddlElements.Axiom;
import pddlElements.Disjunction;
import pddlElements.Domain;
import pddlElements.Effect;


/**
 * @author ignasi
 *
 */
public class Trapper {

	private DirectedMultigraph<String, Edge> kTrapGraph;
	private DefaultDirectedWeightedGraph<String, Edge> CausalGraph;
	private CausalGraph causal;
	private ArrayList<String> goal;
	private ArrayList<Disjunction> disjunctions;
	private Hashtable<Set<String>, Integer> mapping = new Hashtable<Set<String>, Integer>();
	private Integer index = 1;
	private Set<Set<String>> nodes;
	private ArrayList<Set<String>> decoder = new ArrayList<Set<String>>();
	private ArrayList<Axiom> Axioms;
	
	/**
	 * @param cg 
	 * @param set 
	 * @param domain 
	 * @param i 
	 * 
	 */	
	@SuppressWarnings("unused")
	public Trapper(Set<String> literals, Domain domain, CausalGraph cg, int i) {
		kTrapGraph = createStringGraph();
		causal = cg;
		CausalGraph = cg.getGraph();
		goal = domain.goalState;
		disjunctions = domain.list_disjunctions;
		Axioms = domain._Axioms;
		//Dummy node
		addVertex(0);
		decoder.add(new HashSet<String>());		
		/*if(domain.goalState.size()>1){
			createDummyGoalAction(domain);
			literals.add("completed");
			literals.add("~completed");
		}*/
		buildGraph(literals, i);
		createGraph(nodes, domain.list_actions);
		exportGraph();
		System.out.println("Beggining extraction");
		marking();
		//Solver solver = new Solver(cg.getLiterals(), domain._Axioms);
		//eliminateDummyAction(domain);
	}
	
	private void createDummyGoalAction(Domain domain) {
		Action a = new Action();
		a.Name = "Goal-Action";
		a._precond.addAll(domain.goalState);
		Effect e = new Effect();
		e._Effects.add("completed");		
		a._Effects.add(e);
		domain.goalState.clear();
		domain.goalState.add("completed");
	}

	private void exportGraph() {
		try{
			File file = new File("./Ktrap.dot");
			// if file doesnt exists, then create it
			if (!file.exists()) {
				file.createNewFile();
			}
			FileWriter fw = new FileWriter(file.getAbsoluteFile());
			BufferedWriter bw = new BufferedWriter(fw);
			bw.write(printGraph());
			bw.close();
			//System.out.println(graph.toString());
			System.out.println("Ktrap saved in Graph.dot.\n Using graphviz: dot -Tpdf Graph.dot -o Graph.pdf");
		}catch (IOException e1) {
			e1.printStackTrace();
		}
	}
	
	private String printGraph(){
		String contentGraph = "digraph G {\n";
		String edgesGraph = "";
		ArrayList<String> vertex = new ArrayList<String>(kTrapGraph.vertexSet());
		for(String v : vertex){
			contentGraph = contentGraph.concat(cleanStringDot(v) + ";\n");
			List<String> succ = Graphs.successorListOf(kTrapGraph, v);
			edgesGraph = edgesGraph.concat(cleanStringDot(v) + " -> { ");
			for(String e : succ){
				edgesGraph = edgesGraph.concat(cleanStringDot(e) + " ");
			}
			edgesGraph = edgesGraph.concat(" }; \n");
		}
		kTrapGraph.edgeSet();
		return contentGraph + edgesGraph + "}";
	}
	
	private String cleanStringDot(String s){
		s = s.replace("~", "not_");
		return s.replace("-", "");
	}

	
	@SuppressWarnings("rawtypes")
	private DirectedMultigraph<String, Edge> createStringGraph(){
		DirectedMultigraph<String, Edge> g = new DirectedMultigraph<String, Edge>(
	                    new ClassBasedEdgeFactory<String, Edge>(Edge.class));
		return g;		
    }
	
	private void buildGraph(Set<String> literals, int i){
		Set<String> set = new HashSet<String>(literals);
		if(i > 2){
			System.out.println("Too large...exiting");
		}
		if(i == 2){
			nodes = cartesianProduct(set, set);
		}else{
			//Fazer o grafo para conjuntos tamanho 1
		}
	}
	
	private void createGraph(Set<Set<String>> nodes, Hashtable<String, Action> list_actions) {
		for(Set<String> B : nodes){
			//Set<Edge> edges = causal.getOutgoingEdges(B);			
			Integer key = encode(B);
			addVertex(key);
			applyActions(list_actions, B, key);
			applyAxioms(B, key);
		}
	}
	
	private void applyActions(Hashtable<String, Action> list_actions, Set<String> b, Integer bKeyFrom) {
		ArrayList<Action> retList = new ArrayList<Action>();
		for(String a : list_actions.keySet()){
			Action action = list_actions.get(a);
			Set<Set<String>> sucessors;
			if(action.IsObservation){
				if(compatible(b, new HashSet<String>(action._precond)) && compatibleObservation(b, action._Effects)){
					sucessors = solveObservations(b, action._precond, action._Effects);
				}
			}else{
				if(!mutexWithSet(b, new HashSet<String>(action._precond))){
				//if(compatible(b, new HashSet<String>(action._precond))){
					sucessors = solveEffects(b, action._precond, action._Effects);
					if(sucessors.isEmpty()){
						addEdge(bKeyFrom, 0, a);
					}else{
						for(Set<String> sucessor : sucessors){
							Integer to = encode(sucessor);
							addEdge(bKeyFrom, to, a);
						}
					}
				}
			}
		}
		//return retList;
	}
	
	private void addEdge(Integer from, Integer to, String a) {
		if(from.equals(to)){
			return;
		}
		addVertex(from);
		addVertex(to);
		Edge<String> edge = new Edge<String>(from.toString(), to.toString(), a);
		try{
			kTrapGraph.addEdge(from.toString(), to.toString(), edge);
		}catch(Exception e){
			System.out.println("Exception: " + e);
		}
	}

	/**Calculate the next tuples after applying an action. Considering conditional effects*/
	private Set<Set<String>> solveEffects(Set<String> nodes, ArrayList<String> Preconditions, ArrayList<Effect> Effects){
		Set<Set<String>> ret = new HashSet<Set<String>>();
		for(Effect e : Effects){
			if(!mutexWithSet(nodes, new HashSet<String>(e._Condition))){
				ArrayList<String> calc = new ArrayList<String>(nodes);
				calc.addAll(Preconditions);
				HashSet<String> hs = new HashSet<String>(calc);
				hs.addAll(e._Condition);
				calc = new ArrayList<String>(hs);
				for(String eff : e._Effects){
					if(calc.contains(ParserHelper.complement(eff))){
						calc.remove(ParserHelper.complement(eff));
						if(!eff.startsWith("~")) calc.add(eff);
					}else{
						calc.add(eff);
					}
				}
				//calc.addAll(e._Effects);
				if(!(calc.size() == 1) && !nodes.equals(new HashSet<String>(calc))) {
					Set<Set<String>> auxSet = sucessors(calc, nodes);
					if(auxSet.isEmpty()){
						//System.out.println(nodes + " effect : " + e._Condition + e._Effects );
						ret.clear();
						return ret;
					}
					ret.addAll(auxSet);					
				}
			}
		}
		return ret;
	}
	
	/**Solving observations*/
	private Set<Set<String>> solveObservations(Set<String> nodes, ArrayList<String> Preconditions, ArrayList<Effect> Effects){
		Set<Set<String>> ret = new HashSet<Set<String>>();
		ArrayList<String> calc1 = new ArrayList<String>(nodes);
		calc1.addAll(Preconditions);
		ArrayList<String> calc2 = new ArrayList<String>(nodes);
		calc2.addAll(Preconditions);
		for(String observable : Effects.get(0)._Effects){			
			if(calc1.contains(ParserHelper.complement(observable))){
				calc1.remove(ParserHelper.complement(observable));
				//calc1.add(observable);
			}else{
				calc1.add(observable);
			}
			if(calc2.contains(observable)){
				calc2.remove(observable);
				//calc1.add(ParserHelper.complement(observable));
			}else{
				calc2.add(ParserHelper.complement(observable));
			}
		}
		if((calc1.size() == 1) || (calc2.size() == 1) ) {
			//System.out.println(calc);
			//ret.add(new HashSet<String>(calc));
			//Add node to fail?
		}else{
			ret.addAll(sucessors(calc1, nodes));
			ret.addAll(sucessors(calc2, nodes));
		}		
		//ret.addAll(solveAxioms(nodes));
		return ret;
	}
	
	/**Solving axioms: modification of original Ktrap
	 * @param key */
	private void applyAxioms(Set<String> nodes, Integer key){
		Set<Set<String>> ret = new HashSet<Set<String>>();
		for(Axiom a : Axioms){
			if(compatible(nodes, new HashSet<String>(a._Body))){
				Set<Set<String>> sucessors = solveAxioms(nodes, a);
				if(!sucessors.isEmpty()){
					addEdge(key, 0, a._Name);
				}else{
					for(Set<String> sucessor : sucessors){
						Integer to = encode(sucessor);
						addEdge(key, to, a._Name);
					}
				}				
				/*ArrayList<String> calc = solveAxioms(nodes, a);
				ret.addAll(sucessors(calc, nodes));*/
			}
		}
		//return ret;
	}

	private boolean compatibleObservation(Set<String> b, ArrayList<Effect> Effects) {
		if(b.contains(Effects.get(0)._Effects.get(0)) || 
				b.contains(ParserHelper.complement(Effects.get(0)._Effects.get(0)))){
			return false;
		}
		return true;
	}

	private Set<Set<String>> solveAxioms(Set<String> nodes, Axiom axiom) {
		Set<Set<String>> ret = new HashSet<Set<String>>();
		ArrayList<String> calc = new ArrayList<String>(nodes);
		calc.addAll(axiom._Body);
		for(String eff : axiom._Head){
			if(calc.contains(ParserHelper.complement(eff))){
				calc.remove(ParserHelper.complement(eff));
			}else{
				calc.add(eff);
			}
		}
		ret.addAll(sucessors(calc, nodes));
		return ret;
	}

	private Set<Set<String>> sucessors(ArrayList<String> calc, Set<String> kTuple) {
		//if(calc.isEmpty()) System.out.println("Adding dumy node");
		Set<Set<String>> ret = new HashSet<Set<String>>();
		for (Iterator<int[]> iter = new Combinations(calc.size(), 2).iterator(); iter.hasNext();) {
			Set<String> r = new HashSet<String>();
			int[] combination = iter.next();
			r.add(calc.get(combination[0]));
			r.add(calc.get(combination[1]));
			if(r.equals(kTuple)) continue;
			//Verificar que nao sao iguais mas nao aqui!
			if(nodes.contains(r)){
				ret.add(r);
			}
        }
		//If is effect should it be marked as Dummy? or the action itself?
		//If the effect result is empty, it means that the effect transforms the tuple in a Dummy node? 
		return ret;
	}

	private void addVertex(Integer vertex){
		kTrapGraph.addVertex(vertex.toString());
	}
	
	private Integer encode(Set<String> b){
		if(mapping.containsKey(b)){
			return mapping.get(b);
		}else{
			mapping.put(b, index);
			decoder.add(index, b);
			index++;
			return index -1 ;
		}
	}
	
	private Set<String> decode(Integer index){
		return decoder.get(index);
	}

	private Set<Set<String>> cartesianProduct(Set<String> set1, Set<String> set2) {
		Set<Set<String>> product = new HashSet<Set<String>>();
		for(String elem1 : new ArrayList<String>(set1)){
			for(String elem2 : new ArrayList<String>(set2)){
				if(!elem1.equals(elem2) && !areMutex(elem1, elem2)){
					Set<String> s = new HashSet<String>();
					s.add(elem1);
					s.add(elem2);
					if(mutexWithSet(s, new HashSet<String>(goal))) product.add(s);
				}
			}
		}
		return product;
	}
	
	private boolean compatible(Set<String> nodes, HashSet<String> conditions) {
		if(conditions.isEmpty()) return true;
		for(String node : nodes){
			if(conditions.contains(node)){
				return true;
			}
		}
		return false;
	}

	private boolean mutexWithSet(Set<String> nodes, Set<String> setLiterals){
		for(String node : nodes){
			for(String subgoal : setLiterals){
				//if(ParserHelper.isComplement(node, subgoal)){
				if(areMutex(node, subgoal)){
					return true;
				}
			}
			//if(goal.contains(node)) return false;
		}
		return false;
	}

	private boolean areMutex(String l1, String l2){
		if(l1.equals(l2)) return false;
		if(causal.isVariable(l1) && (causal.isVariable(l2)) &&
				l1.substring(0, l1.indexOf("_")).equals(l2.substring(0, l2.indexOf("_"))) ){
			return true;
		}else if(areDisjoint(l1,l2)){
			return true;
		}else if(ParserHelper.isComplement(l1,l2)){
			return true;
		}else{
			return false;
		}
	}
	
	private boolean areDisjoint(String l1, String l2){
		for(Disjunction disj: disjunctions){
			if(disj.hasInside(l1) && disj.hasInside(l2) && !l1.equals(l2)){
				return true;
			}
		}
		return false;
	}
	
	@SuppressWarnings("rawtypes")
	private void marking(){
		Set<String> markedVertex = new HashSet<String>();
		//Start marking from node Dummy
		Stack<String> fringe = new Stack<String>();
		fringe.add("0");
		markedVertex.add("0");
		while(!fringe.isEmpty()){
			String initialNode = fringe.pop();
			//markedVertex.add(initialNode);
			Set<Edge> edges = kTrapGraph.incomingEdgesOf(initialNode);
			for(Edge edge : edges){
				String vertex = kTrapGraph.getEdgeSource(edge);
				if(markedVertex.contains(vertex)) continue;
				if(canMarkNode(markedVertex, edge, vertex)){
					//System.out.println("Added(" + vertex + "): " + decode(Integer.parseInt(vertex)) + " from action: " + edge.toString());
					markedVertex.add(vertex);
					fringe.push(vertex);
				}
			}
		}
		Set<String> notMarked = new HashSet<String>(kTrapGraph.vertexSet());
		notMarked.removeAll(markedVertex);
		printResult(notMarked);
	}

	/*private void printMarking(String vertex) {
		
	}*/

	@SuppressWarnings("rawtypes")
	private boolean canMarkNode(Set<String> markedVertex, Edge edge, String vertex) {
		for(Edge e : kTrapGraph.outgoingEdgesOf(vertex)){
			if(e.toString().equals(edge.toString())){
				if(!markedVertex.contains(kTrapGraph.getEdgeTarget(e))){
					return false;
				}
			}
		}
		return true;
	}
	
	private void printResult(Set<String> traps){
		System.out.println(traps.toString());
		//System.out.println(mapping);
		for(String trap : traps){
			System.out.println(decode(Integer.parseInt(trap)));
		}
	}
	
}
