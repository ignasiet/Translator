/**
 * 
 */
package trapper;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Hashtable;
import java.util.Set;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import parser.ParserHelper;
import pddlElements.Axiom;
import pddlElements.Disjunction;

/**
 * @author ignasi
 *
 */
public class Solver {

	/**
	 * 
	 */
	
	private Set<String> literals;
	private Hashtable<String, Integer> encoder = new Hashtable<String, Integer>();
	private ArrayList<String> decoder = new ArrayList<String>();
	protected ISolver solver;
	private Integer index = 1;
	
    public Solver(Set<String> l, ArrayList<Axiom> Axioms) {
        /*literals = l;
        ISolver solver = SolverFactory.newLight();
        int i = 1;
        for(String literal : literals){
        	map.put(literal.replace("~", ""), i);
        	i++;
        }
        feedCNF(Axioms);*/
    }
    
    public Solver(Hashtable<String, Integer> state, ArrayList<Axiom> _Axioms,
			ArrayList<Disjunction> list_disjunctions) {
    	ISolver solver = SolverFactory.newLight();
    	decoder.add("Dummy");
    	feedInitialState(state);
    	feedAxioms(_Axioms);
    	feedDisjunctions(list_disjunctions);
	}
    
    private void feedDisjunctions(ArrayList<Disjunction> list_disjunctions) {
				
	}

	private void feedAxioms(ArrayList<Axiom> _Axioms) {
    	ArrayList<String> clause = new ArrayList<String>();
		for(Axiom axiom : _Axioms){
			for(String b : axiom._Body){
	    		clause.add(ParserHelper.complement(b));
	    	}
	    	for(String h : axiom._Head){
	    		clause.add(h);
	    	}
		}
		feedCNF(clause);
	}

	private void feedInitialState(Hashtable<String, Integer> state) {
		feedCNF(new ArrayList<String>(state.keySet()));		
	}

	public Integer getId(String literal){
    	if(encoder.containsKey(literal)) return encoder.get(literal);
    	encoder.put(literal, index);
    	decoder.add(index, literal);
    	index++;
    	return index-1;
    }

	public boolean solve(){
    	/*//ISolver solver = SolverFactory.newDefault();
        ISolver solver = SolverFactory.newLight();        
        */
    	solver.setTimeout(3600); // 1 hour timeout
        try {
            IProblem problem = solver;
            if (problem.isSatisfiable()) {
                System.out.println("Satisfiable !");
                return true;
            } else {
                System.out.println("Unsatisfiable !");
                return false;
            }
        } catch (TimeoutException e) {
            System.out.println("Timeout, sorry!");      
        }
        return false;
    }
    
    public void feedCNF(ArrayList<String> clauseRaw){
    	try {
    		int [] clause = parseClauses(clauseRaw);
    		solver.addClause(new VecInt(clause));
		} catch (ContradictionException e) {
			e.printStackTrace();
		}
    }
    
    private int[] parseClauses(ArrayList<String> clauseRaw) {
    	int[] clause = {};
    	for(String lit : clauseRaw){
    		// adapt Array to IVecInt
    		int i;
    		if(lit.startsWith("~")){
    			i = getId(lit.substring(1));
    			i = i* (-1);
    		}else{
    			i = getId(lit);
    		}
    		addElement(clause, i);
    	}
		return clause;
	}

	private static int[] addElement(int[] a, int e) {
        a  = Arrays.copyOf(a, a.length + 1);
        a[a.length - 1] = e;
        return a;
    }
    
    

}
