package pddlElements;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import parser.ParserHelper;


public class Action{
	public ArrayList<String> _precond = new ArrayList<String>();
	//public ArrayList<String> _Positive_effects = new ArrayList<String>();
	//public ArrayList<String> _Negative_effects = new ArrayList<String>();
	public boolean IsObservation = false;
	public boolean _IsConditionalEffect = false;
	public Hashtable<String, ArrayList<String>> action_parameters = new Hashtable<String, ArrayList<String>>();
	public Hashtable<String, String> parameters_type = new Hashtable<String, String>();
	public ArrayList<String> _parameters = new ArrayList<String>();
	public ArrayList<Effect> _Effects = new ArrayList<Effect>();
	public ArrayList<Branch> _Branches = new ArrayList<Branch>();
	public ArrayList<String> parameters_Combination = new ArrayList<String>();
	public boolean deductive_action = false;
	public String combination;
	public String Name;

	public Action(){
		_precond = new ArrayList<String>();
		//_Positive_effects = new ArrayList<String>();
		//_Negative_effects = new ArrayList<String>();
		IsObservation = false;
	}
	
	public void parseParameters(String parametersList){
		String last_object = "";
		ArrayList<String> lista_param = new ArrayList<String>();
		for(String predicate : parametersList.split(" ")){
			if(last_object.equals("-")){
				lista_param.remove(lista_param.size()-1);
				for(String s : lista_param){
					parameters_Combination.add(0, s);
					parameters_type.put(s, predicate);
					_parameters.add(s);
				}
				ArrayList<String> lista_b = new ArrayList<String>(lista_param);
				if(!action_parameters.containsKey(predicate)){
					action_parameters.put(predicate, lista_b);					
				}
				else{
					lista_b.addAll(action_parameters.get(predicate));
					action_parameters.put(predicate, lista_b);
				}
				lista_param.clear();
			}
			else{
				lista_param.add(predicate);				
			}
			last_object = predicate;
		}
	}
	
	public void parsePreconditions(String preconditions_List){
		Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(preconditions_List);
	    while(m.find()) {	    	
    		_precond.add(ParserHelper.cleanString(m.group(1)));
	    }
	}
	
	public void parseEffects(String effect_List){
		Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(effect_List);
		Effect e = new Effect();
		while(m.find()) {
	    	String effect = ParserHelper.cleanString(m.group(1));	    	
	    	//e._Effects.add(effect);
	    	if(effect.startsWith("~")){
	    		e._Effects.add(effect);
	    		//_Negative_effects.add(effect);
	    	}else{
	    		e._Effects.add(effect);
	    		//_Positive_effects.add(effect);
	    	}
	    }
		this._Effects.add(e);
	}
	
	public String ToString(String negateString){
		String auxStr = "";
		if(IsObservation){
			auxStr =  "\n(:observation " + Name;
		}else{
			auxStr = "\n(:action " + Name;
		}
		//Preconditions
		if(_precond.size()>0){
			auxStr = auxStr + "\n:precondition ";
			if(_precond.size()>1){
				auxStr = auxStr + "(and ";
				for(String precond : _precond){
					auxStr = auxStr + ParserHelper.negateString(precond, negateString);
				}
				auxStr = auxStr + ")";
			}
			else{
				for(String precond : _precond){				
					auxStr = auxStr + ParserHelper.negateString(precond, negateString);
				}
			}
		}
		//Effects
		if(!_Effects.isEmpty()){
			auxStr = auxStr + "\n:effect ";
			auxStr = auxStr + "(and ";
			for(Effect ef : _Effects){
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
		if(IsObservation){
			auxStr = auxStr + "\n:branches (or \n";
			for(Branch branch1 : _Branches){
				auxStr = auxStr + branch1.toString(negateString);
				auxStr = auxStr + "\n";
			}
			auxStr = auxStr + ")\n";
		}
		auxStr = auxStr + ")\n";
		return auxStr;
	}
}
