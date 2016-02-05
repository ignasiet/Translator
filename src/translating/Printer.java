package translating;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Enumeration;

import pddlElements.Action;
import pddlElements.Domain;

public class Printer {

	/**
	 * 
	 */
	private static Domain domain;
	private static String negateString = "n_";
	public static void Printer(Domain dom) {
		domain = dom;
		printDomainFile();
		printProblemFile();
	}
	
	private static void printDomainFile(){
		try {
			// Print problem as an XML File
			String path = "src/outputs/Cdomain.pddl";
			File file = new File(path);
			// if file doesnt exists, then create it
			if (!file.exists()) {
				file.createNewFile();
			}
			FileWriter fw = new FileWriter(file.getAbsoluteFile());
			BufferedWriter bw = new BufferedWriter(fw);
			bw.write(printDomain());
			bw.close();

			//System.out.println("Done exporting file to " + path);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	private static void printProblemFile(){
		try {
			// Print problem as an XML File
			String path = "src/outputs/Cproblem.pddl";
			File file = new File(path);
			// if file doesnt exists, then create it
			if (!file.exists()) {
				file.createNewFile();
			}
			FileWriter fw = new FileWriter(file.getAbsoluteFile());
			BufferedWriter bw = new BufferedWriter(fw);
			bw.write(printProblem());
			bw.close();

			//System.out.println("Done exporting file to " + path);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	private static String printDomain() {
		String auxStr = "";
		auxStr = "(define (domain " + domain.Name + ")\n";
		auxStr = auxStr + printTranslatedPredicates();	
		auxStr = auxStr + printActions();
		auxStr = auxStr + "\n)\n";
		return auxStr;
	}
	
	private static String negateString(String pred){
		String auxStr = "";
		if(pred.startsWith("~")){
			auxStr = auxStr + "(not (" + pred.substring(1).replace("~", negateString) + ")) ";
		}
		else{
			auxStr = auxStr + "(" + pred.replace("~", negateString) + ") ";
		}
		return auxStr;
	}
	
	private static String printActions() {
		String auxStr = "";
		Enumeration e = domain.list_actions.keys();
		while(e.hasMoreElements()){
			Action action = domain.list_actions.get(e.nextElement().toString());
			auxStr = auxStr + "\n(:action " + action.Name;
			auxStr = auxStr + "\n:precondition ";
			if(action._precond.size()>1){
				auxStr = auxStr + "(and ";
				for(String precond : action._precond){
					auxStr = auxStr + negateString(precond);
				}
				auxStr = auxStr + ")\n";
			}
			else{
				for(String precond : action._precond){				
					auxStr = auxStr + negateString(precond);
				}
				auxStr = auxStr + "\n";
			}
			auxStr = auxStr + ":effect ";
			auxStr = auxStr + "(and ";
			auxStr = auxStr + ")\n";
			auxStr = auxStr + ")\n";
		}
		return auxStr;
	}

	private static String printTranslatedPredicates() {
		// Print the predicates
		String auxStr = "\n(:predicates ";
		for(String pred : domain.predicates_grounded){
			if(!pred.startsWith("~")){
				auxStr = auxStr + "\n\t(" + pred.replaceAll("~", negateString) + ")";
			}
		}
		auxStr = auxStr + ")\n";
		return auxStr;
	}
	
	private static String printProblem() {
		String auxStr = "";
		auxStr = "(define (problem " + domain.ProblemInstance + ")\n";
		auxStr = auxStr + "(:domain " + domain.Name + ")\n";
		auxStr = auxStr + printInitSituation();
		auxStr = auxStr + printGoalSituation();
		auxStr = auxStr + "\n)\n";
		return auxStr;
	}
	
	private static String printInitSituation() {
		String auxStr = "";
		Enumeration e = domain.state.keys();
		auxStr = auxStr + "(:init \n";
		while(e.hasMoreElements()){
			String pred = e.nextElement().toString();
			if(pred.startsWith("~")){
				auxStr = auxStr + "\t(not (" + pred.replace("~", "") + "))\n ";
			}
			else{
				auxStr = auxStr + "\t(" + pred + ")\n";
			}			
		}
		auxStr = auxStr + ") \n";
		return auxStr;
	}

	private static String printGoalSituation() {
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
	
	

}
