/**
 * 
 */
package pddlElements;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Enumeration;

import parser.ParserHelper;

/**
 * @author ignasi
 *
 */
public class Printer {
	
	private static String negateString = "n_";

	/**Print domain @param arrayList */
	public static void print(String path1, String path2, Domain domain, ArrayList<Action> axioms){
		long startTime = System.currentTimeMillis();
		printDomain(path1, domain, axioms);
		long endTime = System.currentTimeMillis();
		System.out.println("Time printing domain file: " + (endTime - startTime) + " milliseconds");
		startTime = System.currentTimeMillis();		
		printProblem(path2, domain);
		endTime = System.currentTimeMillis();
		System.out.println("Time printing problem file: " + (endTime - startTime) + " milliseconds");
	}
	
	private static void printProblem(String path, Domain domain) {
		try {
			File file = new File(path);
			// if file doesnt exists, then create it
			if (!file.exists()) {
				file.createNewFile();
			}
			FileWriter fw = new FileWriter(file.getAbsoluteFile());
			BufferedWriter bw = new BufferedWriter(fw);
			//bw.write(printProblem(domain));
			bw.write("(define (problem " + domain.ProblemInstance + ")\n");
			bw.write("(:domain " + domain.Name + ")\n");
			//Init
			domain.state.put("Knormal-execution", 1);
			Enumeration<String> e = domain.state.keys();
			bw.write("(:init \n");
			if(domain.costFunction){
				bw.write("(= (total-cost) 0)\n");
			}

			while(e.hasMoreElements()){
				String pred = e.nextElement().toString();
				bw.write("\t" + ParserHelper.createStringPredicate(pred, negateString) + "\n");
			}
			bw.write(") \n");						
			bw.write(printGoalSituation(domain));
			if(domain.costFunction){
				bw.write("(:metric minimize (total-cost)) \n");
			}
			bw.write("\n)\n");
			bw.close();

			//System.out.println("Done exporting file to " + path);
		} catch (IOException e) {
			e.printStackTrace();
		}	
	}

	private static String printGoalSituation(Domain domain) {
		String auxStr = "\n(:goal (and ";
		for(String pred : domain.goalState){
			if (pred.startsWith("~")) {
				auxStr = auxStr + "(not (" + pred.substring(1).replaceAll("~_", negateString) + ")) ";
			} else {
				auxStr = auxStr + "(" + pred.replaceAll("~_", negateString) + ") ";
			}
		}
		auxStr = auxStr + ")\n)";
		return auxStr;
	}

	private static void printDomain(String path, Domain domain, ArrayList<Action> axioms){
		String actName = "";
		try {
			File file = new File(path);
			// if file doesnt exists, then create it
			if (!file.exists()) {
				file.createNewFile();
			}
			FileWriter fw = new FileWriter(file.getAbsoluteFile());
			BufferedWriter bw = new BufferedWriter(fw);
			
			bw.write("(define (domain " + domain.Name + ")\n");
			long startTime = System.currentTimeMillis();
			//bw.write(printPredicates(domain));
			bw.write("\n(:predicates ");
			if(!domain.predicates_grounded.contains("Knormal-execution")){
				domain.predicates_grounded.add("Knormal-execution");
				domain.predicates_grounded.add("Kn_normal-execution");
			}
			for(String pred : domain.predicates_grounded){
				bw.write("\n\t(" + pred.replaceAll("~", negateString) + ")");
			}
			bw.write(")\n");
			if(domain.costFunction){
				bw.write("(:functions (total-cost) ) \n");
			}
			long endTime = System.currentTimeMillis();
			/*Print actions*/
			startTime = System.currentTimeMillis();
			Enumeration<String> e = domain.list_actions.keys();
			while(e.hasMoreElements()){
				Action action = domain.list_actions.get(e.nextElement().toString());
				actName = action.Name;

				//System.out.println("Printing action: " + action.Name);
				bw.write(action.ToString(negateString, domain.costFunction));
			}
			/*Print axioms*/
			for(Action action : axioms){
				//System.out.println("Printing axiom: " + action.Name);
				bw.write(action.ToString(negateString, domain.costFunction));
			}
			//auxStr = auxStr + printActions(domain);
			bw.write("\n)\n");
			endTime = System.currentTimeMillis();
			//System.out.println("Time printing actions in domain file: " + (endTime - startTime) + " milliseconds");
			bw.close();			
		} catch (IOException e) {
			System.out.println("Last action: " + actName);
			e.printStackTrace();
		}
	}
	
	@SuppressWarnings("unused")
	private static String printDomain(Domain domain) {
		String auxStr = "";
		auxStr = "(define (domain " + domain.Name + ")\n";
		auxStr = auxStr + printPredicates(domain);	
		auxStr = auxStr + printActions(domain);
		auxStr = auxStr + "\n)\n";
		return auxStr;
	}

	private static String printActions(Domain domain) {
		String auxStr = "";
		Enumeration<String> e = domain.list_actions.keys();
		while(e.hasMoreElements()){
			Action action = domain.list_actions.get(e.nextElement().toString());
			if(action.IsObservation){
				//auxStr = auxStr + "\n(:observation " + action.Name;
				auxStr = auxStr + "\n(:action " + action.Name;
			}else{
				auxStr = auxStr + "\n(:action " + action.Name;
			}
			//Preconditions
			auxStr = printPreconditions(action, auxStr);
			//Close preconditions			
			//Effects
			if(action.IsObservation){
				printObservation(action, auxStr);
			}else{
				printEffects(action, auxStr);
			}
			auxStr = auxStr + ")\n";
		}
		return auxStr;
	}
	
	private static String printPreconditions(Action action, String auxStr){
		//Preconditions
		if(action._precond.size()>0){
			auxStr = auxStr + "\n:precondition ";
			if(action._precond.size()>1){
				auxStr = auxStr + "(and ";
				for(String precond : action._precond){
					auxStr = auxStr + ParserHelper.createStringPredicate(precond, negateString);
				}
				auxStr = auxStr + ")";
			}
			else{
				for(String precond : action._precond){				
					auxStr = auxStr + ParserHelper.createStringPredicate(precond, negateString);
				}
			}
		}
		return auxStr;
	}
	
	private static String printEffects(Action action, String auxStr){
		//Effects
		if(!action._Effects.isEmpty()){
			auxStr = auxStr + "\n:effect ";
			auxStr = auxStr + "(and ";
			for(Effect ef : action._Effects){
				if(ef._Condition.isEmpty()){
					for(String effect : ef._Effects){
						auxStr = auxStr + ParserHelper.createStringPredicate(effect, negateString);
					}
				}else{
					auxStr = auxStr + "\n(when (and ";
					for(String effect : ef._Condition){
						auxStr = auxStr + ParserHelper.createStringPredicate(effect, negateString);
					}					
					auxStr = auxStr + ") (and ";
					for(String effect : ef._Effects){
						auxStr = auxStr + ParserHelper.createStringPredicate(effect, negateString);
					}
					auxStr = auxStr + "))";
				}
			}
			auxStr = auxStr + ")";
		}
		/*if(action.IsObservation){
			auxStr = auxStr + "\n:branches (or \n";
			for(Branch branch1 : action._Branches){
				auxStr = auxStr + branch1.toString(negateString);
				auxStr = auxStr + "\n";
			}
			auxStr = auxStr + ")\n";
		}*/
		auxStr = auxStr + ")\n";
		return auxStr;
	}
	
	private static String printObservation(Action action, String auxStr){
		if(!action._Effects.isEmpty()){
			auxStr = auxStr + "\n:effect ";
			auxStr = auxStr + "(and ";
		}
		
		/*auxStr = auxStr + "\n:branches (or \n";
		for(Branch branch1 : action._Branches){
			auxStr = auxStr + branch1.toString(negateString);
			auxStr = auxStr + "\n";
		}*/
		auxStr = auxStr + ")\n";
		auxStr = auxStr + ")\n";
		return auxStr;
	}

	private static String printPredicates(Domain domain) {
		// Print the predicates
		String auxStr = "\n(:predicates ";
		for(String pred : domain.predicates_grounded){
			/*if(predicates_initial.containsKey(pred)){
				System.out.println("Repeated element: " + pred);
			}else{
				predicates_initial.put(pred, 1);
			}*/
			if(!pred.startsWith("~")){
				auxStr = auxStr + "\n\t(" + pred.replaceAll("~", negateString) + ")";
			}else{
				System.out.println(pred);
			}
		}
		auxStr = auxStr + ")\n";
		return auxStr;
	}
	
	
}
