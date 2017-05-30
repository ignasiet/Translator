/**
 * 
 */
package planner;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Hashtable;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import pddlElements.Axiom;
import pddlElements.Disjunction;

/**
 * @author Ignasi
 *
 */
public class SATSolver {

	/**
	 * 
	 */
	final  int  MAXVAR = 1000000;
	final  int  NBCLAUSES = 500000;
	
	private Hashtable<String, Integer> mapping = new Hashtable<String, Integer>();
	private int LastIndex = 1;	
	private ArrayList<Integer[]> clauses = new ArrayList<>();
	
	public SATSolver() {
		//Prepare variables:				
		//  prepare  the  solver  to  accept  MAXVAR  variables. MANDATORY
		
		// not  mandatory  for  SAT  solving. MANDATORY  for  MAXSAT  solving
		
		// Feed  the  solver  using  Dimacs  format , using  arrays  of int
		// (best  option  to  avoid  dependencies  on  SAT4J  IVecInt)
		for (int i=0;i< NBCLAUSES;i++) {
		//int []  clause = // get the  clause  from  somewhere
		// the  clause  should  not  contain a 0,
		// only  integer (positive  or  negative)
		// with  absolute  values  less or  equal to  MAXVAR
		// e.g. int []  clause = {1,  -3, 7}; is fine
		//  while  int []  clause = {1,  -3, 7, 0}; is not  fine
		//solver.addClause(new  VecInt(clause )); //  adapt  Array to  IVecInt
		//}
		
		}
	}
	
	public boolean isSolvable(String pred) throws TimeoutException{
		int[] n = new int[1];
		n[0] = getIndex(pred);
		ISolver solver = SolverFactory.newDefault ();
		solver.newVar(MAXVAR);
		solver.setExpectedNumberOfClauses(clauses.size() + 1);		
		for(Integer[] clause : clauses){
			int[] c = new int[clause.length];
			for(int i=0;i<clause.length;i++){
				c[i] = clause[i];
			}
			addClause(c, solver);
		}
		// we are  done. Working  now on the  IProblem  interface
		try {
			solver.addClause(new  VecInt(n ));
		} catch (ContradictionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		IProblem  problem = solver;
		return problem.isSatisfiable();
	}
	
	public void addClause(ArrayList<String> clause){		
		Integer[] cl = new Integer[clause.size()];
		int i = 0;
		for(String s : clause){
			if(s.startsWith("~")){
				cl[i] = getIndex(s) * -1;
			}else{
				cl[i] = getIndex(s);
			}
			i++;
		}
		clauses.add(cl);
		//addClause(cl);
	}
	
	public void addXORClause(Disjunction d){
		Integer[] cl = new Integer[d.getIterator().size()];
		int i = 0;
		if(d.getIterator().size() == 2){
			Integer[] oneof = new Integer[d.getIterator().size()];
			for(String s : d.getIterator()){
				cl[i] = getIndex(s);
				oneof[i] = getIndex(s) * -1;
				i++;
			}
			clauses.add(cl);
			clauses.add(oneof);
		}else{
			for(String s : d.getIterator()){
				cl[i] = getIndex(s);
				Integer[] oneof = new Integer[d.getIterator().size()];
				int j = 0;
				for(String opposed : d.getIterator()){
					if(opposed.equals(s)){
						oneof[j] = mapping.get(s);
					}else{
						oneof[j] = getIndex(opposed) * -1;
					}
					j++;
				}
				clauses.add(oneof);
				i++;
			}
			clauses.add(cl);
		}
		
		
	}
	
	private void addClause(int[] cl, ISolver solver){
		//  adapt  Array to  IVecInt
		try {
			solver.addClause(new  VecInt(cl ));
		} catch (ContradictionException e) {			
			e.printStackTrace();
		}
	}
	
	private int getIndex(String key){
		if(mapping.containsKey(key.replace("~", ""))){
			return mapping.get(key.replace("~", ""));
		}else{
			mapping.put(key.replace("~", ""), LastIndex);
			LastIndex++;
			return mapping.get(key.replace("~", ""));
		}
	}

}
