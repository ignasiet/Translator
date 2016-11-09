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
	public int cost;

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
	    	if(effect.contains("total-cost")){
	    		continue;
	    	}
	    	if(effect.startsWith("~")){
	    		e._Effects.add(effect);
	    		//_Negative_effects.add(effect);
	    	}else{
	    		e._Effects.add(effect);
	    		//_Positive_effects.add(effect);
	    	}
	    }
		_Effects.add(e);
	}
	
	public String ToString(String negateString){
		String auxStr = "";
		if(IsObservation){
			auxStr =  printObservations(auxStr, negateString);
			return auxStr;
		}else{
			auxStr = "\n(:action " + Name;
			//Preconditions
			auxStr = printPreconditions(auxStr, negateString);
			auxStr = printEffects(auxStr, negateString);
			auxStr = auxStr + ")\n";
			return auxStr;
		}
	}
	
	private String printObservations(String auxStr, String negateString) {
		String act = "\n(:action " + Name;
		//auxStr =  "\n(:action sensor-" + Name + "-obs0_DETDUP_0";
		//String auxStr2 = "\n(:action sensor-" + Name + "-obs0_DETDUP_1";
		//Preconditions
		act = act + "\n:precondition (and ";
		//auxStr = printPreconditions(auxStr, negateString);
		//auxStr = printObservations(auxStr, negateString);
		/*auxStr = auxStr + "\n:effect " + "(when (and ";
		auxStr2 = auxStr2 + "\n:effect " + "(when (and ";
		auxStr = auxStr + ParserHelper.createStringPredicate("K_need-post-for-" + Name, negateString);
		auxStr2 = auxStr2 + ParserHelper.createStringPredicate("K_need-post-for-" + Name, negateString);*/
		for(String precond : _precond){
			act = act + ParserHelper.createStringPredicate(precond, negateString);
		}/*
		for(Branch b : _Branches){
			auxStr = auxStr + ParserHelper.createStringPredicate(precond, negateString);
			auxStr2 = auxStr2 + ParserHelper.createStringPredicate(precond, negateString);
		}*/
		act = act + ")";
		act = printSpecialEffectsObs(act, negateString);
		act = act + ")\n";
		/*auxStr = auxStr + ")";
		auxStr = auxStr + _Branches.get(0).toString(negateString);
		auxStr = auxStr + "))\n";
		auxStr2 = auxStr2 + ")";
		auxStr2 = auxStr2 + _Branches.get(1).toString(negateString);
		auxStr2 = auxStr2 + "))\n";*/
		String postObs = printSpecialPostObservation(negateString);
		//return act + auxStr + auxStr2 + postObs;
		return act + postObs;
	}
	
	private String printSpecialEffectsObs(String act, String negateString) {
		act = act + "\n:effect (and ";
		//addPredicate("Knormal-execution");
		//addPredicate("Kn_normal-execution");
		//addPredicate("K_need-post-for-" + a.Name);
		//addPredicate("K_not_need-post-for-" + a.Name);
		act = act + ParserHelper.createStringPredicate("~Knormal-execution", negateString);
		act = act + ParserHelper.createStringPredicate("Kn_normal-execution", negateString);
		act = act + ParserHelper.createStringPredicate("~K_not_need-post-for-" + Name, negateString);
		act = act + ParserHelper.createStringPredicate("K_need-post-for-" + Name, negateString);
		if(cost != 0){
			act = act + "\n(increase (total-cost) " + cost + ")\n";
		}
		act = act + ")";
		return act;
	}

	private String printSpecialPostObservation(String negateString){
		String aux = "\n(:action " + Name + "__post__";
		aux = aux + "\n:precondition (and " + ParserHelper.createStringPredicate("K_need-post-for-" + Name, negateString);
		aux = aux + ")";
		aux = aux + "\n:effect (and ";
		aux = aux + ParserHelper.createStringPredicate("~K_need-post-for-" + Name, negateString);
		aux = aux + ParserHelper.createStringPredicate("~Kn_normal-execution", negateString);
		aux = aux + ParserHelper.createStringPredicate("Knormal-execution", negateString);
		aux = aux + ParserHelper.createStringPredicate("K_not_need-post-for-" + Name, negateString);
		aux = aux + "))\n";
		return aux;
	}

	private String printEffects(String auxStr, String negateString){
		//Effects
		if(!_Effects.isEmpty()){
			auxStr = auxStr + "\n:effect (and ";
			String condEffects = "";
			String auxStrEffects = "";
			for(Effect ef : _Effects){
				if(ef._Condition.isEmpty()){					
					for(String effect : ef._Effects){
						auxStrEffects = auxStrEffects + ParserHelper.createStringPredicate(effect, negateString);
					}
				}else{
					condEffects = condEffects + "\n(when (and ";
					for(String effect : ef._Condition){
						condEffects = condEffects + ParserHelper.createStringPredicate(effect, negateString);
					}					
					condEffects = condEffects + ") (and ";
					for(String effect : ef._Effects){
						condEffects = condEffects + ParserHelper.createStringPredicate(effect, negateString);
					}
					condEffects = condEffects + "))";
				}
			}
			if(auxStrEffects.length() > 1){
				auxStr = auxStr + auxStrEffects + condEffects;
			}else{
				auxStr = auxStr + condEffects;
			}
			if(cost != 0){
				auxStr = auxStr + "(increase (total-cost) " + cost + ")";
			}
			auxStr = auxStr + ")";
		}
		return auxStr;
	}
	
	private String printPreconditions(String auxStr, String negateString){
		//Preconditions
		if(_precond.size()>0){
			auxStr = auxStr + "\n:precondition ";
			if(_precond.size()>1){
				auxStr = auxStr + "(and ";
				for(String precond : _precond){
					auxStr = auxStr + ParserHelper.createStringPredicate(precond, negateString);
				}
				auxStr = auxStr + ")";
			}
			else{
				for(String precond : _precond){				
					auxStr = auxStr + ParserHelper.createStringPredicate(precond, negateString);
				}
			}
		}
		return auxStr;
	}
}
