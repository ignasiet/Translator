package parser;
import java.io.File;
import java.io.FileNotFoundException;
import java.util.Iterator;
import java.util.Scanner;

import pddlElements.Action;
import pddlElements.Domain;
import pddlElements.Effect;
import readers.Atom;
import readers.ExprList;
import readers.PDDLParser;
import readers.PDDLParser.Expr;
import readers.PDDLParser.ParseException;
import readers.PDDLTokenizer;

/**
 * @author ignasi
 *
 */
public class Parser {

	/**
	 * 
	 */
	//private String _PathDomain;
	//private String _PathProblem;
	private ExprList _Problem;
	private Domain _Domain = new Domain();
	
	public Parser(String pathDomain, String pathProblem) {
		//_PathDomain = pathDomain;
		//_PathProblem = pathProblem;
		parsing(pathDomain);
		parsing(pathProblem);
	}
	
	public ExprList parsedProblem(){
		return _Problem;
	}
	
	public Domain getDomain(){
		return _Domain;
	}
	
	private void parsing(String path){
		_Problem = parseDomain(path);
		for(Expr e : _Problem){
			String clean_string = e.toString().replaceAll("[()]", "").trim(); 
			parseType(e.toString(), clean_string.split(" ")[0].replace(":", ""), e);
		}
	}
	
	private void parseType(String element, String type, Expr e){
		//System.out.println("=============================");
		//System.out.println("Tipo: " + type);
		//System.out.println(element);
	    switch (type) {
		case "domain":
			_Domain.Name = element.toString().replaceAll("[()]", "").trim().replace(type, "").trim();
			break;
		case "problem":
			_Domain.ProblemInstance = element.toString().replaceAll("[()]", "").trim().replace(type, "").trim();
			break;
		case "predicates":
			String cleanedElement = element.replace(type, "").trim();
			cleanedElement = cleanedElement.substring(2, cleanedElement.length()).trim().replace("\n", "");
			_Domain.parsePredicates(cleanedElement);
			break;
		case "constants":
		case "objects":
			cleanedElement = element.trim().replace("\n", "");
			_Domain.extract(cleanedElement.substring(2, cleanedElement.length()-1));
			break;
		case "action":
			ExprList eList = (ExprList) e;
			Iterator<Expr> it = eList.iterator();
			Action a = new Action();
			while(it.hasNext()){
				String typePredicate = it.next().toString().replace(":", "");
				String predicate = it.next().toString().trim();
				parseTipedAction(a, typePredicate, predicate);
			}
			/*cleanedElement = element.trim().replace("\n", "");
			cleanedElement = cleanedElement.replaceAll("\\s+", " ");
			String[] splitted_String = cleanedElement.substring(1, cleanedElement.length()-1).trim().split(":");
			 parseAction(splitted_String);*/
			_Domain.addActions(a);
			break;
		case "init":
			eList = (ExprList) e;
			it = eList.iterator();
			/*First next is ":init"*/
			it.next();
			ExprList initList = (ExprList) it.next();
			it = initList.iterator();
			while(it.hasNext()){
				String predicate = it.next().toString().trim();
				if(!predicate.equals("and")){
					_Domain.addInitialPredicate(predicate);
				}
			}
			break;
		case "goal":
			cleanedElement = element.replace(type, "").replaceAll("and", "").trim();
			cleanedElement = cleanedElement.trim().replace("\n", "");
			cleanedElement = cleanedElement.replaceAll("\\s+", " ");
			cleanedElement = cleanedElement.substring(2, cleanedElement.length()-1).trim();
			cleanedElement = cleanedElement.substring(2, cleanedElement.length()-1).trim();
			_Domain.parseGoalState(cleanedElement);
			break;
		default:
			break;
		}
	}
	
	private void parseTipedAction(Action a, String type, String predicate){
		switch (type) {
		case "action":
			a.Name = predicate;
			break;
		case "parameters":
			/*Tirar parentesis*/
			predicate = predicate.substring(1, predicate.length()-1);
			a.parseParameters(predicate);
			break;
		case "precondition":
			/*Tirar parentesis se tiver varios niveis*/
			predicate = cleanParentesis(predicate);
			a.parsePreconditions(predicate);
			break;
		case "observe":
			/*Tirar parentesis*/
			predicate = cleanParentesis(predicate);
			a.IsObservation = true;
			a.parseEffects(predicate);
			break;
		case "effect":
			/*Tirar parentesis*/
			if(predicate.contains("when")){
				a._IsConditionalEffect = true;
				Effect effect = new Effect(predicate);
				a._Effects.add(effect);
			}else{
				predicate = cleanParentesis(predicate);
				a.parseEffects(predicate);
			}			
			break;
		}
	}
	
	@SuppressWarnings("unused")
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

	/*private Action parseAction(String[] splitted_String) {
		Action a = new Action();
		for(String token : splitted_String){
			if(token.length()>0){
				String[] line = token.split(" ");
				String predicates_list = token.replaceAll("and", "").replace(line[0], "").trim();
				if(line[0].equals("action")){
					a.Name = line[1];
				}else if(line[0].equals("parameters")){
					predicates_list = predicates_list.substring(1, predicates_list.length()-1);
					a.parseParameters(predicates_list);
				}else if(line[0].equals("precondition")){
					predicates_list = predicates_list.substring(1, predicates_list.length()-1);
					predicates_list = predicates_list.trim();
					a.parsePreconditions(predicates_list);					
				}else if(line[0].equals("effect")){
					predicates_list = predicates_list.substring(1, predicates_list.length()-1);
					a.parseEffects(predicates_list);
				}else if(line[0].equals("observe")){
					a.IsObservation = true;
					a.parseEffects(predicates_list);
				}
			}
		}
		return a;
	}*/

	private ExprList parseDomain(String path){
		Scanner scan;
		try {
			scan = new Scanner(new File(path));
			String content1 = scan.useDelimiter("\\Z").next();
			scan.close();
			PDDLTokenizer tzr = new PDDLTokenizer(content1);
			PDDLParser parser = new PDDLParser(tzr);
			Expr result = parser.parseExpr();
			ExprList domain = (ExprList) result;
			return domain;
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (ParseException e) {
			e.printStackTrace();
		}
		return null;	
	}
	
	/*private Domain buildDomainProblem(){
		Domain dom = new Domain();
		return dom;
	}*/

}
