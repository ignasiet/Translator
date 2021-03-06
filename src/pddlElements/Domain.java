package pddlElements;
import java.lang.reflect.Array;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import parser.ParserHelper;
import planner.SATSolver;
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
	public Hashtable<String, Integer> count = new Hashtable<String, Integer>();
	public Hashtable<String, Integer> predicates_count = new Hashtable<String, Integer>();
	public HashSet<String> predicates_invariants = new HashSet<String>();
	public HashSet<String> predicates_uncertain = new HashSet<String>();
	public Hashtable<String, Integer> predicates_negat = new Hashtable<String, Integer>();
	public Hashtable<String, Integer> predicates_posit = new Hashtable<String, Integer>();
	public Hashtable<String, Integer> predicates_never = new Hashtable<String, Integer>();
	public Hashtable<String, Integer> predicates_invariants_grounded = new Hashtable<String, Integer>();
	public ArrayList<String> goalState = new ArrayList<String>();
	public Hashtable<String, ArrayList<String>> variables = new Hashtable<String, ArrayList<String>>();
	public Action disjunctionAction = new Action();
	public String ProblemInstance;
	private Integer counter = 0;
	public ArrayList<Axiom> _Axioms = new ArrayList<Axiom>();
	public ArrayList<ArrayList<String>> specialAxioms = new ArrayList<ArrayList<String>>();
	public boolean costFunction = false;
	public SATSolver sat = new SATSolver();
	public HashSet<String> observables = new HashSet<String>();
	public Hashtable<String, ArrayList<String>> related = new Hashtable<String, ArrayList<String>>();
	public HashSet<String> UncertainPredicates = new HashSet<String>();
	public HashSet<String> obsPredicates = new HashSet<String>();
	public Hashtable<String, ArrayList<ArrayList<String>>> ruleSet = new Hashtable<>();
	public Hashtable<String, ArrayList<ArrayList<String>>> relevanceSet = new Hashtable<>();
	public Hashtable<String,ArrayList<String>> freeVars = new Hashtable<String,ArrayList<String>>();
	private HashSet<String> invariants = new HashSet<String>();
	private HashSet<String> negatInvariants = new HashSet<String>();


	public void parsePredicates(String predicates_list){
		Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(predicates_list);
	    while(m.find()) {	    	
	    	predicates.add(m.group(1));
	    }
	    //predicates.add("lock");
	}
	
	public void addActions(Action a){
		action_list.add(a);
		initStateVariables(a);
	}
	
	private void countPredicates(){
		//Refazer!!!!
		int val = 0;
		for(Action a : action_list){
			Hashtable<String, Integer> countV = new Hashtable<String, Integer>();
			for(Effect e : a._Effects){
				String cleanS ="";
				for(String s : e._Effects){
					val = (s.startsWith("~")) ? -1 : 1;
					cleanS = s.replace("~", "");
					cleanS = (cleanS.contains("_")) ? cleanS.substring(0, cleanS.indexOf("_")) : cleanS;
					if(!countV.containsKey(cleanS)){
						countV.put(cleanS, val);
					}else{
						int v = countV.get(cleanS) + val;
						countV.put(cleanS, v);
					}
				}
				for(String key : countV.keySet()){
					updateValue(key, countV.get(key));
				}
				/*if(count.containsKey(cleanS)){
					int maxval = Math.max(count.get(cleanS), val);
					count.put(cleanS, maxval);
				}else{
					count.put(cleanS, val);
				}*/
			}
		}
	}
	
	private void updateValue(String key, int value){
		if(!count.containsKey(key)){
			count.put(key, value);
		}else{
			int maxval = Math.max(count.get(key), value);
			count.put(key, maxval);
		}
	}
	
	public void detectInvariants(){
		ArrayList<String> invar = new ArrayList<String>();
		for(String p : predicates){
			int aux = p.indexOf(" ");
			if(aux > 0){
				invar.add(p.substring(0, aux));
			}else{
				invar.add(p);
			}
		}
		for(Action action : action_list){
			if(action.IsObservation) continue;
			for(Effect eff : action._Effects){
				for(String s : eff._Effects){
					if(s.startsWith("~")) continue;
					if(invar.contains(ParserHelper.extractRoot(s))) invar.remove(ParserHelper.extractRoot(s));
				}
			}
			for(Branch br : action._Branches){
				for(String s : br._Branches){
					if(s.startsWith("~")) continue;
					if(invar.contains(ParserHelper.extractRoot(s))) invar.remove(ParserHelper.extractRoot(s));
				}
			}
		}
		invariants.addAll(invar);
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

	public boolean ground_all_actions() {
		countPredicates();
		boolean grounded = false;
		for(Action a : action_list){
			if(!a._parameters.isEmpty()){
				ground_actions(a);			
			}else{
				grounded = true;
				System.out.println("Action already instantiated: " + a.Name);
				list_actions.put(a.Name, a);
			}
		}
		return grounded;
	}
	
	private void getNeverHappen() {
		Hashtable<String, Integer> variant_predicates = new Hashtable<String, Integer>(predicates_negat);		
		variant_predicates.keySet().retainAll(predicates_posit.keySet());
		//System.out.println(inersect);
		System.out.println("Variable fluents: " + variant_predicates.keySet().toString());
		variant_predicates = new Hashtable<String, Integer>(predicates_negat);
		variant_predicates.keySet().removeAll(predicates_posit.keySet());
		Enumeration<String> e = variant_predicates.keys();
		while(e.hasMoreElements()){
			String p = e.nextElement().toString();
			if(state.containsKey(p) || UncertainPredicates.contains(p)){
				variant_predicates.remove(p);
			}
		}
		for(Axiom ax : _Axioms){
			for(String sAx : ax._Head){
				variant_predicates.remove(sAx);
			}
		}
		System.out.println("Not used fluent: " + variant_predicates.keySet().toString());
		predicates_never = new Hashtable<String, Integer>(variant_predicates);
	}
	
	public void getInvariantPredicates(){
		HashSet<String> predicates_variants = new HashSet<String>();
		for(String p : predicates){
			int aux = p.indexOf(" ");
			if(aux > 0){
				predicates_invariants.add(p.substring(0, aux));
			}else{
				predicates_invariants.add(p);
			}
		}
		/*for(Disjunction disj : list_disjunctions){
			//predicates_variants.put(disj.getFluent(), 1);
			predicates_uncertain.add(disj.getFluent());
		}*/
		Enumeration<String> e = list_actions.keys();
		while(e.hasMoreElements()){
			Action a = list_actions.get(e.nextElement().toString());
			//No single effects: now all are cond effects
			if(a._IsNondeterministic){
				for(Branch b : a._Branches){
					for(String nFluent : b._Branches){
						if(!nFluent.startsWith("~")){
							predicates_posit.put(nFluent, 1);
						}else{
							nFluent = nFluent.replace("~", "");
							predicates_negat.put(nFluent, 1);
						}
						nFluent = nFluent.replace("~", "");
						if(nFluent.contains("_")){
							predicates_variants.add(nFluent.substring(0, nFluent.indexOf("_")));
						}else{
							predicates_variants.add(nFluent);
						}
						if(a._parameters.isEmpty() && !predicates_grounded.contains(nFluent)) predicates_grounded.add(nFluent);
					}
				}
			}
			for(Effect effect : a._Effects){
				for(String eff : effect._Effects){
					if(!eff.startsWith("~")){
						predicates_posit.put(eff, 1);
					}else{						
						eff = eff.replace("~", "");
						predicates_negat.put(eff, 1);
					}
					eff = eff.replace("~", "");
					if(eff.contains("_")){
						predicates_variants.add(eff.substring(0, eff.indexOf("_")));
					}else{
						predicates_variants.add(eff);
					}
					if(a._parameters.isEmpty() && !predicates_grounded.contains(eff)) predicates_grounded.add(eff);
				}
			}
		}
		predicates_variants.addAll(predicates_uncertain);
		predicates_invariants.removeAll(predicates_variants);
	}
	
	public boolean isUncertain(String predicate){
		predicate = predicate.replace("~", "");
		for(Disjunction disj: list_disjunctions){
			if(disj.hasInside(predicate)){
				return true;
			}
		}
		return false;
	}
	
	private boolean isInstantiatedUncertain(String predicate){
		predicate = predicate.replace("~", "");
		for(Disjunction disj: list_disjunctions){
			if(disj.contains(predicate)){
				return true;
			}
		}
		return false;
	}
	
	public boolean isInvariant(String predicate){
		if(predicate.contains("_")){
			predicate = predicate.substring(0, predicate.indexOf("_"));
		}
		//Consider also negated literals
		if(predicates_invariants.contains(predicate.replace("~", ""))){
			return true;
		}else{
			return false;
		}
	}

	public boolean isObservable(String obs){
		return observables.contains(obs.substring(0, obs.indexOf("_")).replace("~", ""));
	}
	
	public void eliminateInvalidActions(){
		getNeverHappen();
		Enumeration<String> e = list_actions.keys();
		ArrayList<String> actions_to_be_removed = new ArrayList<String>();
		while(e.hasMoreElements()){
			String action_name = e.nextElement().toString();
			Action a = list_actions.get(action_name);
			for(String precond : a._precond){
				if(isInvariant(precond) && !isUncertain(precond)){
					predicates_grounded.remove(precond);
					/* Verify 2 things:
					 * 1 - Does it happens in initial state?
					 * 2 - Is it an uncertainty predicate?
					 */
					if(!isUncertain(precond) && !state.containsKey(precond)){
						actions_to_be_removed.add(action_name);
					}
				}
				if(predicates_never.containsKey(precond) ){
					System.out.println("Imposible predicate?: " + precond + " " + action_name);
					predicates_grounded.remove(precond);
					actions_to_be_removed.add(action_name);
				}
			}
		}
		list_actions.keySet().removeAll(actions_to_be_removed);
	}
	
	public void eliminateUselessEffects(){
		Enumeration<String> e = list_actions.keys();
		while(e.hasMoreElements()){
			String action_name = e.nextElement().toString();
			Action a = list_actions.get(action_name);
			ArrayList<Integer> effectsToEliminate = new ArrayList<Integer>();
			int i = 0;
			for(Effect effect : a._Effects){
				for(String cond : effect._Condition){
					if(isUseless(cond)){
						System.out.println("Eliminating effect in action " + a.Name);
						effectsToEliminate.add(i);
					}
				}
				i++;
			}
			for(Integer in : effectsToEliminate){
				Effect uselessEffect = a._Effects.get(in);
				a._Effects.remove(uselessEffect);
			}			
		}
	}

	@SuppressWarnings({ "unchecked", "unused" })
	public void ground_actions(Action action){
		ArrayList<String> result = new ArrayList<String>();
		Enumeration<String> e = action.action_parameters.keys();
		Enumeration<String> en = action.parameters_type.keys();
		for(String element : action.parameters_Combination){
			result = product(constantes.get(action.parameters_type.get(element)), result);
		}
		for(String combination : result){
			boolean validAction = validCombination(combination, action._precond, action._parameters);
			if(!validAction) continue;
			Action act_grounded = new Action();
			act_grounded.cost = action.cost;
			if(action.IsObservation){
				act_grounded.IsObservation = true;
			}
			if(action._IsNondeterministic){
				act_grounded._IsNondeterministic = true;
			}
			act_grounded.combination = combination;
			act_grounded.Name = action.Name + "_" + combination.replace(";", "_");
			ArrayList<String> lista_objetos = new ArrayList<String>(Arrays.asList(combination.split(";")));
			int i = 0;
			String precond = action._precond.toString().replace("[", "").replace("]", "");
			for(String parameter : action._parameters){
				precond = precond.replace(parameter, lista_objetos.get(i));
				i++;
			}
			ArrayList<String> lista_precond = new ArrayList<String>();
			for(String item : Arrays.asList(precond.split(","))){
				lista_precond.add(item.trim());
				if(item.contains("=")) continue;
				if(!predicates_count.containsKey(item.trim())){
					predicates_grounded.add(item.trim());
					predicates_count.put(item.trim(), 1);
				}
			}
			act_grounded._precond = lista_precond;
			act_grounded.cleanEqualityPred();
			if(validAction){
				act_grounded._parameters.addAll(action._parameters);
				for(Effect effect : action._Effects){
					if(!effect._Condition.isEmpty()){
						act_grounded._IsConditionalEffect = true;
					}
					act_grounded._Effects.add(groundEffect(effect, act_grounded));
				}					
				//groundEffects(act_grounded);
				if(act_grounded._IsNondeterministic){
					for(Branch br : action._Branches){
						act_grounded._Branches.add(groundBranches(br, act_grounded));
					}
				}
				list_actions.put(act_grounded.Name, act_grounded);
			}			
		}
	}

	/*private boolean consistenObservation(String combination, ArrayList<String> Parameters){
		return UncertainPredicates.contains()
	}*/
	
	private boolean validCombination(String combination, ArrayList<String> Precond, ArrayList<String> Parameters){
		for(String p : Precond){
			if(p.contains("=")){
				String[] params = combination.split(";");
				int i = 0;
				int j = 0;
				String[] aux = new String[2];
				for(String pr : Parameters){
					if(p.contains(pr)){
						aux[j] = params[i];
						j++;
					}
					i++;
				}
				if(p.startsWith("~")){
					if(aux[0].equals(aux[1])){
						return false;
					}
				}else{
					if(!aux[0].equals(aux[1])){
						return false;
					}
				}
			}else if(invariants.contains(ParserHelper.extractRoot(p))){
				String[] params = combination.split(";");
				int i = 0;
				String aux = p;
				for(String pr : Parameters){
					aux = aux.replace(pr, params[i]);
					i++;
				}
				if(!state.containsKey(aux) && !UncertainPredicates.contains(aux)) return false;
			}
		}
		return true;
	}
	
	private Branch groundBranches(Branch br, Action act_grounded){
		Branch b = new Branch();
		ArrayList<String> lista_objetos = new ArrayList<String>(Arrays.asList(act_grounded.combination.split(";")));
		ArrayList<String> list_effects = new ArrayList<String>();
		String eff_effect = br._Branches.toString().replace("[", "").replace("]", "");
		int i = 0;
		for(String parameter : act_grounded._parameters){
			eff_effect = eff_effect.replace(parameter, lista_objetos.get(i));
			i++;
		}
		for(String item : Arrays.asList(eff_effect.split(","))){
			list_effects.add(item.trim());
			if(!predicates_count.containsKey(item.replace("~", "").trim())){
				predicates_grounded.add(item.replace("~", "").trim());
				predicates_count.put(item.replace("~", "").trim(), 1);
			}
		}		
		b._Branches = list_effects;
		return b;
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
	
	private boolean isUseless(String pred){
		if(isInvariant(pred) && !state.containsKey(pred) && !isInstantiatedUncertain(pred)){
			System.out.println("Useless predicate found: " + pred);
			return true;
		}else{
			return false;
		}
	}

	public void parseGoalState(String goal_state){
		//Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(goal_state);
		Matcher m = Pattern.compile("\\((.*?)\\)").matcher(goal_state);
	    while(m.find()) {
	    	String aux = m.group(1);
	    	aux = aux.replace("(", "").trim();
	    	goalState.add(ParserHelper.cleanString(aux));
	    }
	}

	public void addInitialPredicate(String initial_state){
		if(initial_state.contains("(oneof")){
			int index_oneof = initial_state.indexOf("(oneof") + 6;
			String oneof_string = initial_state.substring(index_oneof);
			Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(oneof_string);
			Disjunction disj = new Disjunction();
			while(m.find()) {
				String aux = ParserHelper.cleanString(m.group(1));
				//disj.add(aux);
				UncertainPredicates.add(disj.add(aux));
			}
			sat.addXORClause(disj);
			list_disjunctions.add(disj);
			initial_state = initial_state.substring(0, index_oneof);
			//addDeductiveOneOfAction(disj);
		}else if(initial_state.contains("(unknown")){
			System.out.println("Predicate with initial uncertainty: " + initial_state);
		}else if(initial_state.contains("total-cost")){
			System.out.println("Domain with costs");
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
			if(clause.size()>2){
				specialAxioms.add(clause);
			}
			//Prepare clauses for SAT SOLVER
			sat.addClause(clause);
			relateTo(clause);
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
				if(UncertainPredicates.contains(elem)){
					addRelevanceSet(elem, a_1._Body);
				}else{
					if(!isObservable(elem) && !elem.startsWith("~")) addRuleSet(elem, a_1._Body);
				}
				_Axioms.add(a_1);
			}
		}
		counter++;
	}

	private void addRuleSet(String elem, ArrayList<String> body) {
		for(String p : body){
			if(UncertainPredicates.contains(p.replace("~", ""))) return;
		}
		if(ruleSet.containsKey(elem)){
			ArrayList<ArrayList<String>> newList = new ArrayList<ArrayList<String>>(ruleSet.get(elem));
			newList.add(body);
			ruleSet.put(elem, newList);
		}else{
			ArrayList<ArrayList<String>> newList = new ArrayList<ArrayList<String>>();
			newList.add(body);
			ruleSet.put(elem, newList);
		}
	}

	private void addRelevanceSet(String elem, ArrayList<String> body){
		if(relevanceSet.containsKey(elem)){
			ArrayList<ArrayList<String>> newList = new ArrayList<ArrayList<String>>(relevanceSet.get(elem));
			newList.add(body);
			relevanceSet.put(elem, newList);
		}else{
			ArrayList<ArrayList<String>> newList = new ArrayList<ArrayList<String>>();
			newList.add(body);
			relevanceSet.put(elem, newList);
		}
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

	public void addObservable(String predicate) {
		//observables.add(predicate.substring(0, predicate.indexOf(" ")).replace("(", ""));
		observables.add(predicate.substring(0, predicate.indexOf("_")));
	}

	/*TODO: implement function Related to, where every threat (pit_X or wumpus_X)
	 is related to a oneof element (safe_X)
	* */
	private void relateTo(ArrayList<String> axiom){
		String flag = null;
		for(String ex : axiom){
			String pred = ParserHelper.cleanString(ParserHelper.cleanSpaces(ex));
			for(Disjunction d : list_disjunctions){
				if(d.contains(pred.replace("~", ""))){
					flag = pred.replace("~", "");
					d.derivates.addAll(axiom);
					d.axioms.add(axiom);
					d.extractVars(pred, axiom);
					break;
				}
			}
		}
		if(flag!=null){
			for(String p : axiom) {
				if(p.replace("~", "").equals(flag)) continue;
				updateRelated(flag, p);
			}
		}
	}

	public void updateRelated(String pred, String key){
		if(related.containsKey(key)){
			ArrayList<String> oldContent = new ArrayList<>(related.get(key));
			oldContent.add(pred);
			related.put(key, oldContent);
		}else{
			ArrayList<String> nContent = new ArrayList<>();
			nContent.add(pred);
			related.put(key, nContent);
		}
	}

	public ArrayList<String> opositeObs(String predicate) {
		String prefix = predicate.replace("~", "").substring(0, predicate.indexOf("_")-1);
		String pos = predicate.substring(predicate.indexOf("_"));
		ArrayList<String> r = new ArrayList<String>();
		for(String o : observables){
			if(!o.equals(prefix)){
				r.add("~" + o + pos);
			}
		}
		return r;
	}

	//TODO: Identify variables
	public void initStateVariables(Action a) {
		for(Effect e : a._Effects){
			for(String effect : e._Effects){
				String eff = effect;
				if(effect.contains("_")){
					eff = effect.substring(0, effect.indexOf("_"));
				}
				if(eff.startsWith("~")){
					updateCounter(eff.substring(1), -1);
				}else{
					updateCounter(eff, 1);
				}
			}
		}
	}

	private void updateCounter(String pred, int c){
		if(count.containsKey(pred)){
			count.put(pred, count.get(pred) + c);
		}else{
			count.put(pred, c);
		}
	}

	public void getMutexFree() {
		//freeVars = new HashSet<String>();
		for (Action a : action_list) {
			if(a.IsObservation) continue;
			for(String parameter : a._parameters){
				if((a.affectedPrec(parameter)) && !a.affectedEff(parameter) && !a.affectedBranches(parameter)){
					//freeVars.put(parameter);
					if(freeVars.containsKey(a.parameters_type.get(parameter))){
						ArrayList<String> oldList = new ArrayList<String>(
								freeVars.get(a.parameters_type.get(parameter)));
						freeVars.put(a.parameters_type.get(parameter), oldList);
					}else{
						ArrayList<String> oldList = new ArrayList<String>();
						oldList.add(parameter);
						freeVars.put(a.parameters_type.get(parameter), oldList);
					}
				}
			}
		}
	}

	public void reInitialState() {
		HashMap<String, Integer> co = new HashMap<String, Integer>();
		for(String c : state.keySet()){
			if(!c.contains("_")) continue;
			String p = c.replace("~", "").substring(0, c.indexOf("_"));
			if(!co.containsKey(p)){
				co.put(p, 1);
			}else{
				co.put(p, co.get(p)+1);
			}
		}

		for(String predicate : co.keySet()){
			if(count.containsKey(predicate) && count.get(predicate)==0){
				ArrayList<String> values = new ArrayList<String>();
				for(String pred : predicates_grounded){
					if(pred.startsWith(predicate)) values.add(pred);
				}
				variables.put(predicate, values);
			}
		}
	}

	public ArrayList<String> getInvariantsPosit(){
		ArrayList<String> retList = new ArrayList<String>();
		for(String predicate : predicates_posit.keySet()){
			if(!isUncertain(predicate) && !isObservable(predicate)){
				retList.add(predicate);
			}
		}
		return retList;
	}

	public boolean inGoal(String prec) {
		if(!prec.contains("_")){
			return goalState.contains(prec);
		}
		for(String goal : goalState){
			if(goal.contains(prec.substring(0, prec.indexOf("_")))) return true;
		}
		return false;
	}
}
