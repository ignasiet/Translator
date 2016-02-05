package pddlElements;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import parser.ParserHelper;
import readers.ExprList;
import readers.PDDLParser.Expr;


public class Domain {
	
	public String Name;
	//public String wumpus;
	public ArrayList<Action> action_list = new ArrayList<Action>();
	public ArrayList<String> predicates = new ArrayList<String>();
	public ArrayList<String> predicates_grounded = new ArrayList<String>();
	public ArrayList<Disjunction> list_disjunctions = new ArrayList<Disjunction>();
	@SuppressWarnings("rawtypes")
	public Hashtable<String, ArrayList> constantes = new Hashtable<String, ArrayList>();
	public Hashtable<String, Action> list_actions = new Hashtable<String, Action>();
	public Hashtable<String, Integer> state = new Hashtable<String, Integer>();
	public Hashtable<String, Integer> hidden_state = new Hashtable<String, Integer>();
	public Hashtable<String, Integer> predicates_count = new Hashtable<String, Integer>();
	public Hashtable<String, Integer> predicates_invariants = new Hashtable<String, Integer>();
	public Hashtable<String, Integer> predicates_invariants_grounded = new Hashtable<String, Integer>();
	public ArrayList<String> goalState = new ArrayList<String>();
	public Action disjunctionAction = new Action();
	public String ProblemInstance;
	private Integer counter = 0;
	public ArrayList<Axiom> _Axioms = new ArrayList<Axiom>();
	
	
	public void parsePredicates(String predicates_list){
		Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(predicates_list);
	    while(m.find()) {	    	
	    	predicates.add(m.group(1));
	    }
	    //predicates.add("lock");
	}
	
	public void addActions(Action a){
		action_list.add(a);
	}
	
	@SuppressWarnings("unchecked")
	public void extract(String objects){
		String[] splited_objects = objects.split(" ");
		String last_object = "";
		ArrayList<String> lista_objetos = new ArrayList<String>(Arrays.asList(splited_objects));
		ArrayList<String> lista_predicados = new ArrayList<String>();
		lista_objetos.remove(0);
		for(String predicate : lista_objetos){
			if(last_object.equals("-")){
				lista_predicados.remove(lista_predicados.size()-1);
				ArrayList<String> lista_b = new ArrayList<String>(lista_predicados);
				if(constantes.containsKey(predicate)){
					ArrayList<String> list_a = constantes.get(predicate);
					list_a.addAll(lista_b);
					constantes.put(predicate, list_a);
				}else{
					constantes.put(predicate, lista_b);
				}
				lista_predicados.clear();
			}
			else{
				lista_predicados.add(predicate);
			}
			last_object = predicate;
		}
	}
	
	public static ArrayList<String> product(ArrayList<String> list1, ArrayList<String> list2){
		if(list2.isEmpty()){
			return list1;
		}
		else{
			ArrayList<String> result = new ArrayList<String>();
			for(String element1 : list1){
				for(String element2: list2){
					if(!element1.equals(element2)){
						result.add(element1 + ";" + element2);
					}
				}
			}
			return result;
		}
	}

	public void ground_all_actions() {
		for(Action a : action_list){
			ground_actions(a);
		}
	}
	
	public void getInvariantPredicates(){
		Hashtable<String, Integer> predicates_variants = new Hashtable<String, Integer>();
		Enumeration<String> e = list_actions.keys();
		while(e.hasMoreElements()){
			Action a = list_actions.get(e.nextElement().toString());
			//No single effects: now all are cond effects
			for(Effect effect : a._Effects){
				for(String eff : effect._Effects){
					eff = eff.replace("~", "");
					if(eff.contains("_")){
						predicates_variants.put(eff.substring(0, eff.indexOf("_")), 1);
					}else{
						predicates_variants.put(eff, 1);
					}
				}				
			}
		}
		for(Action a : action_list){
			for(String predicate : a._precond){
				String auxPredicate = predicate;
				if(predicate.contains("_")){
					auxPredicate = predicate.substring(0, predicate.indexOf("_"));
				}
				if(!predicates_variants.containsKey(auxPredicate) & !isUncertain(auxPredicate)){
					predicates_invariants.put(auxPredicate, 1);
				}
			}
			for(Effect eff : a._Effects){
				for(String eff_cond : eff._Condition){
					String auxPredicate = eff_cond;
					if(eff_cond.contains("_")){
						auxPredicate = eff_cond.substring(0, eff_cond.indexOf("_"));
					}
					if(!predicates_variants.containsKey(auxPredicate) & !isUncertain(auxPredicate)){
						predicates_invariants.put(auxPredicate, 1);
					}
				}
			}
		}
	}
	
	private boolean isUncertain(String predicate){
		for(Disjunction disj: list_disjunctions){
			if(disj.hasInside(predicate)){
				return true;
			}
		}
		return false;
	}
	
	public void eliminateInvalidActions(){
		Enumeration<String> e = list_actions.keys();
		ArrayList<String> actions_to_be_removed = new ArrayList<String>();
		while(e.hasMoreElements()){
			String action_name = e.nextElement().toString();
			Action a = list_actions.get(action_name);
			for(String precond : a._precond){
				String predicate_name = precond;
				if(precond.contains("_")){
					predicate_name = precond.substring(0, precond.indexOf("_"));
				}
				if(predicates_invariants.containsKey(predicate_name)){
					predicates_invariants_grounded.put(precond, 1);
					predicates_grounded.remove(precond);
					/*
					 * Verify 2 things:
					 * 1 - Does it happens in initial state?
					 * 2 - Is it an uncertainty predicate?
					 */
					if(!state.containsKey(precond)){
						for(Disjunction elems : list_disjunctions){
							if(!elems.contains(precond)){
								actions_to_be_removed.add(action_name);
								break;
							}
						}
					}
				}
			}
			for(Effect effect : a._Effects){
				for(String cond_effect : effect._Condition){
					String predicate_name = cond_effect;
					if(cond_effect.contains("_")){
						predicate_name = cond_effect.substring(0, cond_effect.indexOf("_"));
					}
					if(predicates_invariants.containsKey(predicate_name)){
						predicates_invariants_grounded.put(cond_effect, 1);
						predicates_grounded.remove(cond_effect);
						if(!state.containsKey(cond_effect)){
							for(Disjunction elems : list_disjunctions){
								if(!elems.contains(cond_effect)){
									actions_to_be_removed.add(action_name);
									break;
								}
							}
						}
					}
				}
			}
		}
		for(String deleteAction : actions_to_be_removed){
			/*if(deleteAction.contains("move_p5-3_")){
				System.out.println(deleteAction);
			}*/
			list_actions.remove(deleteAction);
		}
	}
	
	@SuppressWarnings({ "unchecked", "unused" })
	public void ground_actions(Action action){
		ArrayList<String> result = new ArrayList<String>();
		//Hashtable<String, String> substitution = new Hashtable<String, String>();
		Enumeration<String> e = action.action_parameters.keys();
		Enumeration<String> en = action.parameters_type.keys();
		//Grounding errors: bad combinations. Use parameters_combination		
		/*while(en.hasMoreElements()){
			String parameter = en.nextElement().toString();
			result = product(constantes.get(action.parameters_type.get(parameter)), result);
		}*/
		//String parameter = en.nextElement().toString();
		for(String element : action.parameters_Combination){
			result = product(constantes.get(action.parameters_type.get(element)), result);
		}
		for(String combination : result){
			boolean validAction = true;
			Action act_grounded = new Action();
			if(action.IsObservation){
				act_grounded.IsObservation = true;
			}
			act_grounded.combination = combination;
			act_grounded.Name = action.Name + "_" + combination.replace(";", "_");
			ArrayList<String> lista_objetos = new ArrayList<String>(Arrays.asList(combination.split(";")));
			int i = 0;
			//String posit_eff = action._Positive_effects.toString().replace("[", "").replace("]", "");
			//String negat_eff = action._Negative_effects.toString().replace("[", "").replace("]", "");
			String precond = action._precond.toString().replace("[", "").replace("]", "");
			for(String parameter : action._parameters){
				//String parameter = e.nextElement().toString();
				//posit_eff = posit_eff.replace(parameter, lista_objetos.get(i));
				//negat_eff = negat_eff.replace(parameter, lista_objetos.get(i));
				precond = precond.replace(parameter, lista_objetos.get(i));
				i++;
			}
			//ArrayList<String> lista_efeitos_positivos = new ArrayList<String>();
			//ArrayList<String> lista_efeitos_negativos = new ArrayList<String>();
			/*for(String item : Arrays.asList(posit_eff.split(","))){
				lista_efeitos_positivos.add(item.trim());
				if(!predicates_count.containsKey(item.trim())){
					predicates_grounded.add(item.trim());
					predicates_count.put(item.trim(), 1);
				}
			}
			for(String item : Arrays.asList(negat_eff.split(","))){
				lista_efeitos_negativos.add(item.trim());
				if(!predicates_count.containsKey(item.trim())){
					predicates_grounded.add(item.trim());
					predicates_count.put(item.trim(), 1);
				}
			}*/
			ArrayList<String> lista_precond = new ArrayList<String>();
			for(String item : Arrays.asList(precond.split(","))){
				lista_precond.add(item.trim());
				if(!predicates_count.containsKey(item.trim())){
					predicates_grounded.add(item.trim());
					predicates_count.put(item.trim(), 1);
				}
			}
			//act_grounded._Positive_effects = lista_efeitos_positivos;
			//act_grounded._Negative_effects = lista_efeitos_negativos;
			act_grounded._precond = lista_precond;
			if(validAction){
				act_grounded._parameters.addAll(action._parameters);
				for(Effect effect : action._Effects){
					if(!effect._Condition.isEmpty()){
						act_grounded._IsConditionalEffect = true;
					}
					act_grounded._Effects.add(groundEffect(effect, act_grounded));
				}					
				//groundEffects(act_grounded);
				list_actions.put(act_grounded.Name, act_grounded);
			}
		}
	}
	
	private Effect groundEffect(Effect eff, Action act_grounded){
		Effect e = new Effect();
		ArrayList<String> lista_objetos = new ArrayList<String>(Arrays.asList(act_grounded.combination.split(";")));
		ArrayList<String> list_cond = new ArrayList<String>();
		ArrayList<String> list_effects = new ArrayList<String>();
		String cond_eff = eff._Condition.toString().replace("[", "").replace("]", "");
		String eff_effect = eff._Effects.toString().replace("[", "").replace("]", "");
		int i = 0;
		for(String parameter : act_grounded._parameters){
			cond_eff = cond_eff.replace(parameter, lista_objetos.get(i));
			eff_effect = eff_effect.replace(parameter, lista_objetos.get(i));
			i++;
		}
		for(String item : Arrays.asList(cond_eff.split(","))){
			list_cond.add(item.trim());
		}
		for(String item : Arrays.asList(eff_effect.split(","))){
			list_effects.add(item.trim());
		}
		if(!eff._Condition.isEmpty()){
			e._Condition = list_cond;
		}		
		e._Effects = list_effects;
		return e;
	}
	
	/*private void groundEffects(Action act_grounded){
		ArrayList<String> lista_objetos = new ArrayList<String>(Arrays.asList(act_grounded.combination.split(";")));
		int i = 0;
		for(int j=0; j<act_grounded._Effects.size();j++){
			Effect in = act_grounded._Effects.get(j);
			ArrayList<String> lista_cond = new ArrayList<String>();
			String cond_eff = in._Condition.toString().replace("[", "").replace("]", "");
			ArrayList<String> lista_efeitos = new ArrayList<String>();			
			String eff = in._Effects.toString().replace("[", "").replace("]", "");
			for(String parameter : act_grounded._parameters){
				cond_eff = cond_eff.replace(parameter, lista_objetos.get(i));
				eff = eff.replace(parameter, lista_objetos.get(i));
				i++;
			}
			for(String item : Arrays.asList(cond_eff.split(","))){
				lista_cond.add(item.trim());
			}
			for(String item : Arrays.asList(eff.split(","))){
				lista_efeitos.add(item.trim());
			}
			act_grounded._Effects.remove(j);
			if(!in._Condition.isEmpty()){
				in._Condition = lista_cond;
			}			
			in._Effects = lista_efeitos;
			act_grounded._Effects.add(in);
		}
	}*/
	
	public void parseGoalState(String goal_state){
		Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(goal_state);
	    while(m.find()) {	    	
	    	goalState.add(ParserHelper.cleanString(m.group(1)));
	    }
	}
	
	/*public void addInitialState(String initial_state){
		if(initial_state.contains("(oneof")){
			int index_oneof = initial_state.indexOf("(oneof") + 6;
			String oneof_string = initial_state.substring(index_oneof);
			Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(oneof_string);
		    while(m.find()) {
		    	String aux = ParserHelper.cleanString(m.group(1));
		    	predicates_uncertain.add(aux);
		    }
		    initial_state = initial_state.substring(0, index_oneof);
		    addDeductiveOneOfAction();
		}
		Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(initial_state);
	    while(m.find()) {
	    	String auxString = ParserHelper.cleanString(m.group(1));
	    	if(!predicates_count.containsKey(auxString)){
	    		predicates_count.put(auxString, 1);
	    		predicates_grounded.add(auxString);
	    		if(auxString.contains("wumpus")){
	    			wumpus = auxString;
	    			System.out.println("Wumpus escolhido em: " + auxString);
	    		}
	    	}
	    	state.put(auxString, 1);
	    }
	}*/
	
	public void addInitialPredicate(String initial_state){
		if(initial_state.contains("(oneof")){
			int index_oneof = initial_state.indexOf("(oneof") + 6;
			String oneof_string = initial_state.substring(index_oneof);
			Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(oneof_string);
			Disjunction disj = new Disjunction();
		    while(m.find()) {
		    	String aux = ParserHelper.cleanString(m.group(1));
		    	disj.add(aux);
		    }
		    list_disjunctions.add(disj);
		    initial_state = initial_state.substring(0, index_oneof);
		    //addDeductiveOneOfAction(disj);
		}else if(initial_state.contains("(unknown")){
			//TODO: consider unknown predicates?
			System.out.println("Predicate with initial uncertainty: " + initial_state);
		}else if(initial_state.contains("(or")){
			addAxioms(initial_state);
		}else{
			String auxString = ParserHelper.cleanString(initial_state);
			state.put(auxString, 1);
		}
	}
	
	@SuppressWarnings("unused")
	private void addAxioms(String axiom){
		ExprList eList = new ExprList();
		if((eList = ParserHelper.parse(axiom)) != null){
			boolean isFirst = true;
			//Clause with more than 2 predicates -> should be translated as a exhaustive combination
			//Formula: F0 or...or Fi or ... or Fn should be translated as:
			// not F0 and ... and not Fi-1 and not Fi+1 and ... and not Fn -> Fi			
			ArrayList<String> clause = new ArrayList<String>();
			for(Expr ex : eList){
				if(!ex.toString().equals("or")){
					String pred = ParserHelper.cleanString(ParserHelper.cleanSpaces(ex.toString()));
					clause.add(pred);
				}
			}
			for(String elem : clause){
				Axiom a_1 = new Axiom();
				a_1._Name = counter + "-" + elem;
				//Body: condition
				//Head: effect
				a_1._Head.add(elem);
				for(String other_elems : clause){
					if(!other_elems.equals(elem)){
						a_1._Body.add(ParserHelper.complement(other_elems));
					}
				}
				_Axioms.add(a_1);
			}			
		}
		counter++;
	}
	
	public void addHiddenState(String initial_state){
		Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(initial_state);
	    while(m.find()) {
	    	String auxString = ParserHelper.cleanString(m.group(1));
	    	hidden_state.put(auxString, 1);
	    }
	}

	public String sensingAction(String action_name){
		String observation = "";
		Action a = list_actions.get(action_name.toLowerCase());
		//TODO: Sensing actions yield only one predicate?
		Effect e = a._Effects.get(0);
		String predicate_observed = e._Effects.get(0);
		//if not, correct lines above
		if(hidden_state.containsKey(predicate_observed)){
			observation = predicate_observed;
		}else{
			observation = "~" + predicate_observed;
		}
		if(observation.startsWith("~")){
			state.remove(observation.substring(1));
			hidden_state.remove(observation.substring(1));
		}else{
			state.put(observation, 1);
			hidden_state.put(observation, 1);
		}		
		return observation;
	}
}
