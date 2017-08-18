package pddlElements;
import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.sun.org.apache.xalan.internal.xsltc.compiler.Parser;

import parser.ParserHelper;
import readers.Atom;
import readers.ExprList;
import readers.PDDLParser;
import readers.PDDLTokenizer;
import readers.PDDLParser.Expr;

/**
 * @author ignasi
 *
 */
public class Effect {
	public ArrayList<String> _Condition = new ArrayList<String>();
	public ArrayList<String> _Effects = new ArrayList<String>();	
	
	public Effect(){}
	
	public Effect(String conditionalEffect){
		conditionalEffect = conditionalEffect.replaceAll("and", "").replaceAll("\\s+", " ").trim();
		ExprList eList = new ExprList();
		if((eList = ParserHelper.itemize(conditionalEffect)) != null){
			/* Parsing conditional effect: 3 elements
			 * 1- "when"
			 * 2- Conditions: index 1
			 * 3- Effects: index 2
			 * */
			String effectsList = eList.get(2).toString().trim();
			effectsList = cleanParentesis(effectsList);
			parsePreconditions(effectsList, "effects");
			String conditionsList = eList.get(1).toString().trim();
			conditionsList = cleanParentesis(conditionsList);
			parsePreconditions(conditionsList, "cond");
			//Here start modification
			
			//End modification
			/*String el = eList.get(2).toString().trim();
			el = el.substring(1, el.length()-1);
			el = ParserHelper.cleanString(el);
			Clean string
			_Effects.add(el.trim().replace(" ", "_"));*/
			//Modification starts here
			/*el = eList.get(1).toString().trim();
			el = el.substring(1, el.length()-1);
			el = ParserHelper.cleanString(el);*/
			//Ends here
			/*Clean string*/
			//_Condition.add(el.replace(" ", "_"));
		}
	}
	
	private void parsePreconditions(String preconditions_List, String what){
		Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(preconditions_List);		
	    while(m.find()) {
	    	if(what.equals("cond")){
				_Condition.add(ParserHelper.cleanString(m.group(1)));
			}else{
				_Effects.add(ParserHelper.cleanString(m.group(1)));
			}
	    }
	}
	
	private String cleanParentesis(String predicate) {
		predicate = predicate.replaceAll("and", "").replaceAll("\\s+", " ").trim();
		Atom at = new Atom(predicate);
		Expr ex = (Expr) at;
		try{
			PDDLTokenizer tzr = new PDDLTokenizer(predicate);
			PDDLParser parser = new PDDLParser(tzr);
			Expr result = parser.parseExpr();
			ExprList eList = (ExprList) result;
			ExprList elements = (ExprList) eList.get(0);
			return predicate.substring(1, predicate.length()-1);
		}catch(Exception excp){
			return predicate;
		}
	}

	public boolean affectedPred(String predicate){
		for(String eff : _Effects){
			if(eff.contains(predicate)){
				return true;
			}
		}
		return false;
	}
}
