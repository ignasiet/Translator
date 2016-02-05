/**
 * 
 */
package pddlElements;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Enumeration;

import parser.ParserHelper;

/**
 * @author ignasi
 *
 */
public class Printer {
	
	private static String negateString = "n_";
	//private static Hashtable<String, Integer> predicates_initial = new Hashtable<String, Integer>();
	/**Print domain*/
	public static void print(String path1, String path2, Domain domain){
		long startTime = System.currentTimeMillis();
		printDomain(path1, domain);
		long endTime = System.currentTimeMillis();
		//System.out.println("Time printing domain file: " + (endTime - startTime) + " milliseconds");
		startTime = System.currentTimeMillis();		
		printProblem(path2, domain);
		endTime = System.currentTimeMillis();
		//System.out.println("Time printing problem file: " + (endTime - startTime) + " milliseconds");
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
			Enumeration<String> e = domain.state.keys();
			bw.write("(:init \n");
			while(e.hasMoreElements()){
				String pred = e.nextElement().toString();
				bw.write("\t" + ParserHelper.negateString(pred, negateString) + "\n");
			}
			bw.write(") \n");
			bw.write(printGoalSituation(domain));
			bw.write("\n)\n");
			bw.close();

			//System.out.println("Done exporting file to " + path);
		} catch (IOException e) {
			e.printStackTrace();
		}	
	}

	@SuppressWarnings("unused")
	private static String printProblem(Domain domain) {
		String auxStr = "";
		auxStr = "(define (problem " + domain.ProblemInstance + ")\n";
		auxStr = auxStr + "(:domain " + domain.Name + ")\n";
		auxStr = auxStr + printInitSituation(domain);
		auxStr = auxStr + printGoalSituation(domain);
		auxStr = auxStr + "\n)\n";
		return auxStr;
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

	private static String printInitSituation(Domain domain) {
		String auxStr = "";
		Enumeration<String> e = domain.state.keys();
		auxStr = auxStr + "(:init \n";
		while(e.hasMoreElements()){
			String pred = e.nextElement().toString();
			if(pred.startsWith("~")){
				auxStr = auxStr + "\t(not " + pred.replaceAll("~", negateString) + ")\n ";
			}
			else{
				auxStr = auxStr + "\t" + ParserHelper.negateString(pred, negateString) + "\n";
			}			
		}
		auxStr = auxStr + ") \n";
		return auxStr;
	}

	private static void printDomain(String path, Domain domain){
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
			for(String pred : domain.predicates_grounded){
				bw.write("\n\t(" + pred.replaceAll("~", negateString) + ")");
			}
			bw.write(")\n");
			long endTime = System.currentTimeMillis();
			//System.out.println("Time printing predicates in domain file: " + (endTime - startTime) + " milliseconds");
			//System.out.println("Predicates printed");
			startTime = System.currentTimeMillis();
			Enumeration<String> e = domain.list_actions.keys();
			while(e.hasMoreElements()){
				Action action = domain.list_actions.get(e.nextElement().toString());
				bw.write(action.ToString(negateString));
			}
			//auxStr = auxStr + printActions(domain);
			bw.write("\n)\n");
			endTime = System.currentTimeMillis();
			//System.out.println("Time printing actions in domain file: " + (endTime - startTime) + " milliseconds");
			bw.close();
			
		} catch (IOException e) {
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
				auxStr = auxStr + "\n(:observation " + action.Name;
			}else{
				auxStr = auxStr + "\n(:action " + action.Name;
			}
			//Preconditions
			if(action._precond.size()>0){
				auxStr = auxStr + "\n:precondition ";
				if(action._precond.size()>1){
					auxStr = auxStr + "(and ";
					for(String precond : action._precond){
						auxStr = auxStr + ParserHelper.negateString(precond, negateString);
					}
					auxStr = auxStr + ")";
				}
				else{
					for(String precond : action._precond){				
						auxStr = auxStr + ParserHelper.negateString(precond, negateString);
					}
				}
			}
			//Close preconditions			
			//Effects
			if(!action._Effects.isEmpty()){
				auxStr = auxStr + "\n:effect ";
				auxStr = auxStr + "(and ";
				for(Effect ef : action._Effects){
					if(ef._Condition.isEmpty()){
						for(String effect : ef._Effects){
							auxStr = auxStr + ParserHelper.negateString(effect, negateString);
						}
					}else{
						auxStr = auxStr + "\n(when (and ";
						for(String effect : ef._Condition){
							auxStr = auxStr + ParserHelper.negateString(effect, negateString);
						}					
						auxStr = auxStr + ") (and ";
						for(String effect : ef._Effects){
							auxStr = auxStr + ParserHelper.negateString(effect, negateString);
						}
						auxStr = auxStr + "))";
					}
				}
				auxStr = auxStr + ")";
			}
			if(action.IsObservation){
				auxStr = auxStr + "\n:branches (or \n";
				for(Branch branch1 : action._Branches){
					auxStr = auxStr + branch1.toString(negateString);
					auxStr = auxStr + "\n";
				}
				auxStr = auxStr + ")\n";
			}
			auxStr = auxStr + ")\n";
		}
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
