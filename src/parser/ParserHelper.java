/**
 * 
 */
package parser;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;

import pddlElements.Action;
import pddlElements.Domain;
import pddlElements.Effect;
import readers.ExprList;
import readers.PDDLParser;
import readers.PDDLParser.Expr;
import readers.PDDLParser.ParseException;
import readers.PDDLTokenizer;

/**
 * @author ignasi
 *
 */
public class ParserHelper {

	/**
	 * 
	 */
	public static void ParserHelper() {
		// TODO Auto-generated constructor stub
	}
	
	public static ExprList itemize(String predicate){
		PDDLTokenizer tzr = new PDDLTokenizer(predicate);
		PDDLParser parser = new PDDLParser(tzr);
		Expr result;
		try {
			result = parser.parseExpr();
			ExprList eList = (ExprList) result;
			if(eList.size()>1){
				return eList;
			}else{
				ExprList elements = (ExprList) eList.get(0);
				return elements;
			}			
		} catch (ParseException e) {
			//e.printStackTrace();
			return null;
		}
	}
	
	public static int countElements(String predicate){
		PDDLTokenizer tzr = new PDDLTokenizer(predicate);
		PDDLParser parser = new PDDLParser(tzr);
		Expr result;
		try {
			result = parser.parseExpr();
			ExprList eList = (ExprList) result;
			return eList.size();
		} catch (ParseException e) {
			e.printStackTrace();
			return 0;
		}
		
	}
	
	public static ExprList parse(String predicate){
		PDDLTokenizer tzr = new PDDLTokenizer(predicate);
		PDDLParser parser = new PDDLParser(tzr);
		Expr result;
		try {
			result = parser.parseExpr();
			ExprList eList = (ExprList) result;
			return eList;
		} catch (ParseException e) {
			//e.printStackTrace();
			return null;
		}
	}
	
	public static String cleanString(String a){
		a = a.replace("and", "").replaceAll("\\n", "");
		if(a.startsWith("not")){
			a = a.replaceAll("[()]", "").replace("not ", "").trim();
			a = a.replace(" ", "_");
			a = "~" + a;
		}else{
			a = a.replaceAll("[()]", "").replace("not ", "~").replace(" ", "_").trim();
		}
		return a;
	}
	
	public static String cleanSpaces(String a){
		a = a.replaceAll("\\s+", " ").trim();
		return a;
	}
	
	public static String complement(String a){
		if(a.startsWith("~")){
			return a.substring(1);
		}else{
			return "~" + a;
		}
	}
	
	public static boolean isInvariant(String p, Domain domain) {
		String[] pSplitted = p.split("_");
		if(domain.predicates_invariants.containsKey(pSplitted[0])){
			return true;
		}else{
			return false;
		}		
	}
	
	public static String negateString(String pred, String negateString){
		String auxStr = "";
		if(pred.startsWith("~")){
			auxStr = auxStr + "(not (" + pred.substring(1).replace("~", negateString) + ")) ";
		}
		else{
			auxStr = auxStr + "(" + pred.replace("~", negateString) + ") ";
		}
		return auxStr;
	}
	
	public static Domain cleanProblem(Domain domain){
		//1 - clean goal
		ArrayList<String> newGoal = new ArrayList<String>();
		Hashtable<String, Integer> newState = new Hashtable<String, Integer>();
		for(String predicate : domain.goalState){
			if(!isInvariant(predicate, domain)){
				newGoal.add(predicate);
			}
		}
		domain.goalState = newGoal;
		//2 - clean state
		Enumeration<String> e = domain.state.keys();
		while(e.hasMoreElements()){
			String predicate = e.nextElement().toString();
			if(!isInvariant(predicate, domain)){
				newState.put(predicate, 1);
			}
		}
		domain.state = newState;
		//3 - clean actions
		Enumeration<String> actions = domain.list_actions.keys();
		while(actions.hasMoreElements()){
			String action_name = actions.nextElement().toString();
			ArrayList<String> newPrecond = new ArrayList<String>();
			ArrayList<String> newCond = new ArrayList<String>();
			Action action = domain.list_actions.get(action_name);
			//Clean preconditions
			for(String precond : action._precond){
				if(!isInvariant(precond, domain)){
					newPrecond.add(precond);
				}
			}
			action._precond = newPrecond;
			//Clean conditions (cond. effects)
			for(Effect eff : action._Effects){
				for(String cond : eff._Condition){
					if(!isInvariant(cond, domain)){
						newCond.add(cond);
					}
				}
				eff._Condition = newCond;
			}
			
		}
		//TODO: 4- Clean predicates 
		return domain;
	}

}
