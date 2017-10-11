/**
 * 
 */
package parser;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import pddlElements.Action;
import pddlElements.Branch;
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
		String p = predicate.replace("not", "");
		PDDLTokenizer tzr = new PDDLTokenizer(p);
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
	
	private static void parse(String list, ArrayList<String> Branches) {
		PDDLTokenizer tzr = new PDDLTokenizer(list);
		PDDLParser parser = new PDDLParser(tzr);
		Expr result;
		try {
			result = parser.parseExpr();
			ExprList eList = (ExprList) result;
			Iterator<Expr> it = eList.iterator();
			while(it.hasNext()){
				String s = it.next().toString().trim();
				if(s.equals("and")) continue;
				Branches.add(cleanString(s));
			}
		} catch (ParseException e) {
			//e.printStackTrace();
		}		
	}
	
	public static int ParseCost(String s){
		// increase (total-cost) 10
		String pattern = "\\(total-cost\\)\\s*(\\d+)";		
		// Create a Pattern object
	    Pattern r = Pattern.compile(pattern, Pattern.DOTALL);
	    // Now create matcher object.
	    Matcher m = r.matcher(s);
	    if(m.find()) {
	    	int cost = Integer.parseInt(m.group(1).trim());
	    	return cost;
	    }else {
	    	System.out.println("NO MATCH");
	    	return (Integer) null;
	    }
		//String[] aux = s.replaceAll("\\s+", " ").split(" ");		
	}

	//TODO: Non deterministic actions
	public static Branch[] extractNonDeterministicBranches(String s){
		Branch b1 = new Branch();
		Branch b2 = new Branch();
		ExprList e = new ExprList();
		
		if((e = ParserHelper.itemize(s)) != null){
			if(countElements(e.get(1).toString()) > 1){
				parse(e.get(1).toString(), b1._Branches);
			}else{
				String listEffects = cleanString(e.get(1).toString());
				b1._Branches.add(listEffects);
			}
			if(countElements(e.get(2).toString()) > 1){
				parse(e.get(2).toString(), b2._Branches);
			}else{
				String listEffects = cleanString(e.get(2).toString());
				b2._Branches.add(listEffects);
			}
			/*String branch1 = cleanString(e.get(1).toString().trim());
			b1._Branches.add(branch1);
			String branch2 = cleanString(e.get(2).toString().trim());
			b2._Branches.add(branch2);*/
		}
		Branch[] branches = new Branch[2];
		branches[0] = b1;
		branches[1] = b2;
		return branches;
	}

	public static String cleanString(String a){
		a = a.replace("and", "").replaceAll("\\n", "").replaceAll("\\s+", " ").trim();
		if(a.startsWith("not") && !a.startsWith("not-")){
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
	
	public static boolean isComplement(String a, String b){
		if(complement(a).equals(b)){
			return true;
		}else{
			return false;
		}
	}
	
	public static String extractRoot(String a){
		if(!a.contains("_")){
			return a;
		}else{
			return a.substring(0, a.indexOf("_"));
		}
	}

	public static String extractKRoot(String a){
		String aux;
		if(!a.contains("_")){
			aux = a;
		}else{
			aux = a.substring(0, a.indexOf("_"));
		}
		return aux.substring(1).replace("~", "");
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
		if(domain.predicates_invariants.contains(pSplitted[0])){
			return true;
		}else{
			return false;
		}		
	}
	
	public static String createStringPredicate(String pred, String negateString){
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
				eff._Condition = (ArrayList<String>) newCond.clone();
				newCond.clear();
			}			
		}

		return domain;
	}

}
