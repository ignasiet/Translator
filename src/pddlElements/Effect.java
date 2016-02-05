package pddlElements;
import java.util.ArrayList;

import parser.ParserHelper;
import readers.ExprList;

/**
 * @author ignasi
 *
 */
public class Effect {
	public ArrayList<String> _Condition = new ArrayList<String>();
	public ArrayList<String> _Effects = new ArrayList<String>();	
	
	public Effect(){}
	
	public Effect(String conditionalEffect){
		_Condition = new ArrayList<String>();
		conditionalEffect = conditionalEffect.replaceAll("and", "").replaceAll("\\s+", " ").trim();
		ExprList eList = new ExprList();
		if((eList = ParserHelper.itemize(conditionalEffect)) != null){
			/* Parsing conditional effect: 3 elements
			 * 1- "when"
			 * 2- Conditions: index 1
			 * 3- Effects: index 2
			 * */
			String el = eList.get(2).toString().trim();
			el = el.substring(1, el.length()-1);
			_Effects.add(el.trim().replace(" ", "_"));
			el = eList.get(1).toString().trim();
			el = el.substring(1, el.length()-1);
			_Condition.add(el.replace(" ", "_"));
		}
	}
	
}
