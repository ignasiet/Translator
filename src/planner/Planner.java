package planner;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import HHCP.*;
import landmark.Landmarker;
import parser.Parser;
import parser.ParserHelper;
import pddlElements.*;
import pddlElements.Printer;
import translating.*;
import causalgraph.CausalGraph;


public class Planner {
	public static Domain domain = new Domain();
	public static Domain domain_translated = new Domain();
	private static String outputPath = "";
	private static CausalGraph cg;
	private static ArrayList<String> _Plan = new ArrayList<>();
	private static Hashtable<String, String> _ObservationSelected = new Hashtable<String, String>();
	private static boolean changes = false;
	private static String algorithm = "";
	
	public static void startPlanner(String domain_file_path, String problem_file_path,
									String file_out_path, String type, boolean ontop, String heuristic,
									long cost, String alg){
		/*Define problem*/
		if(!(file_out_path == null)){
			outputPath = file_out_path;
		}
		algorithm = alg;
		long startTime = System.currentTimeMillis();
		initDomain(domain_file_path, problem_file_path);
		long endTime = System.currentTimeMillis();
		System.out.println("Preprocessing time: " + (endTime - startTime) + " milliseconds");
		/*Time measure: translation*/
		domain = ParserHelper.cleanProblem(domain);
		if(domain.UncertainPredicates.isEmpty()){
			fondPlanner(heuristic, cost);
		}else{
			contingentPlanner(ontop, type, file_out_path, heuristic, cost);
		}
	}

	private static void fondPlanner(String heuristic, long cost) {
		Problem p = transformToVectors(domain, false, null, domain.variables);
		Problem hP = transformToVectors(domain, true, null, domain.variables);

		System.out.println("Transformation to vectors completed. ");

		//LANDMARKS
		Landmarker l = new Landmarker(domain.state, domain.list_actions, domain.goalState);

		cg = new CausalGraph(domain_translated);
		HashSet<String> relevants = cg.relevantLiterals(domain_translated.goalState);

		if(changes) {
			p = transformToVectors(domain_translated, false, null, domain.variables);
			hP = transformToVectors(domain_translated, true, null, domain.variables);
		}
		JustificationGraph jG = new JustificationGraph(hP);
		jG.setRelevantLiterals(hP, relevants);

		System.out.println("Init Search. ");

		//Simulator sim = new Simulator(null, p.getInitState(), p, hP);
		if(algorithm.equals("lrtdp")) {
			LRTDP lrtdp = new LRTDP(p, hP, new ArrayList<String>(), jG, heuristic, cost);
		}else if(algorithm.equals("maxprob")){
			MaxProb mprob = new MaxProb(p, hP, new ArrayList<String>(), jG, heuristic, cost);
		}else{
			LCGRTDP lcrtdp = new LCGRTDP(p, hP, new ArrayList<String>(), jG, heuristic, cost);
		}
	}

	private static void contingentPlanner(boolean ontop, String type, String file_out_path, String heuristic, long cost){
		/*cg = new CausalGraph(domain);
		HashSet<String> relevants = cg.relevantLiterals(domain.goalState);*/

		//UncertaintyGraph uG = new UncertaintyGraph(domain);
		long startTime = System.currentTimeMillis();
		/*Set size of the ksets to 2*/
		//Trapper tp = new Trapper(cg.getLiterals(), domain, cg, 2);
		if(ontop){
			addFlags();
		}
		Translation tr = translate(type, domain);
		//LinearTranslation tr = new LinearTranslation(domain);
		long endTime = System.currentTimeMillis();
		System.out.println("Translation time: " + (endTime - startTime) + " Milliseconds");
		domain_translated = tr.getDomainTranslated();
		domain_translated.hidden_state = domain.hidden_state;


		Problem p = transformToVectors(domain_translated, false, tr.getListAxioms(), domain.variables);
		Problem hP = transformToVectors(domain_translated, true, tr.getListAxioms(), domain.variables);

		System.out.println("Transformation to vectors completed. ");
		//LANDMARKS
		//Landmarker l = new Landmarker(domain_translated.state, domain_translated.list_actions, domain_translated.goalState);

		addSpecialActions(hP, ontop);
		cg = new CausalGraph(domain_translated);
		HashSet<String> relevants = cg.relevantLiterals(domain_translated.goalState);

		/*Print domain*/
		if(!(file_out_path == null)) printDomain(tr);

		if(changes) {
			p = transformToVectors(domain_translated, false, tr.getListAxioms(), domain.variables);
			hP = transformToVectors(domain_translated, true, tr.getListAxioms(), domain.variables);
		}
		JustificationGraph jG = new JustificationGraph(hP);
		jG.setRelevantLiterals(hP, relevants);

		System.out.println("Init Search. ");


		if(algorithm.equals("lrtdp")) {
			LRTDP lrtdp = new LRTDP(p, hP, new ArrayList<String>(), jG, heuristic, cost);
		}else if(algorithm.equals("maxprob")){
			HMaxProb mprob = new HMaxProb(p, hP, new ArrayList<String>(), jG, heuristic, cost);
		}else{
			LCGRTDP lcrtdp = new LCGRTDP(p, hP, new ArrayList<String>(), jG, heuristic, cost);
		}
	}

	private static Problem transformToVectors(Domain domain_translated, boolean isHeuristic, ArrayList<Action> listAxioms, Hashtable<String, ArrayList<String>> variables) {
		/*Planner: review grounded literals*/
		HHCP.Problem p;
		if(domain_translated.predicates_grounded.isEmpty()){
			p = new Problem(new ArrayList<String>(domain_translated.predicates_posit.keySet()), variables);
		}else{
			p = new Problem(domain_translated.predicates_grounded, variables);
		}
		p.setInitState(domain_translated.state);
		p.setGoalState(domain_translated.goalState);

		if(isHeuristic){
			for(String name : domain_translated.list_actions.keySet()) {
				Action a = domain_translated.list_actions.get(name);
				if(!a.IsObservation && !a._IsNondeterministic){
					p.insertAction(a, false);
				}else{
					p.determinizeBranches(a);
				}
			}
			for(String pred : domain.UncertainPredicates){
				p.uncertainty.add(p.getPredicate("K" + pred));
				p.uncertainty.add(p.getPredicate("K~" + pred));
			}
			for(String pred : domain.obsPredicates){
				p.observables.add(p.getPredicate("K"+pred));
			}
		}else{
			p.setActions(domain_translated.list_actions);
		}
		if(listAxioms != null) {
			p.setAxioms(listAxioms);
		}
		p.setVectorCosts();
		return p;
	}

	private static void addFlags() {
		domain.predicates_grounded.add("not-started");
		domain.state.put("not-started", 1);
		for(String name : domain.list_actions.keySet()){
			Action action = domain.list_actions.get(name);
			if(action._Effects.isEmpty()) action._Effects.add(new Effect());
			if(!action.IsObservation){
				action._Effects.get(0)._Effects.add("~not-started");
			}
		}
	}

	private static void addHumanInterventionActions(int cost, boolean ontop){
		//Add human observations
		ArrayList<String> replaceObjects = new ArrayList<String>();
		ArrayList<String> replacingActions = new ArrayList<String>();
		for(String object : domain.constantes.keySet()){
			if(domain.freeVars.containsKey(object)){
				replaceObjects.addAll(domain.constantes.get(object));
			}
		}
		for(String name : domain.list_actions.keySet()){
			Action a = domain_translated.list_actions.get(name);
			if(a == null) continue;
			//Human observations
			Action a_old = domain.list_actions.get(name);
			if(a.IsObservation){
				addHumanObservation(a, a_old, cost, ontop);
			}else{
				for(String obj : replaceObjects){
					if(a.Name.contains("_" + obj)){
						for(String prec : a._precond){
							if(domain_translated.inGoal(prec)) continue;
							if(prec.contains(obj) && !replacingActions.contains(prec)){
								replacingActions.add(prec);
							}
						}
					}
				}
			}
		}
		addObjectAction(replacingActions, cost);
		domain_translated.costFunction = true;
	}

	private static void addObjectAction(ArrayList<String> replacingActions, int cost) {
		for(String element : replacingActions){
			Action a_human = new Action();
			a_human.Name = "Modify_human_" + element;
			a_human.cost = 10*cost;
			if(element.startsWith("K")){
				a_human._precond.add("K~" + element.substring(1));
			}else{
				a_human._precond.add(ParserHelper.complement(element));
			}
			//a_human._precond.add("Knot-started");
			Effect e = new Effect();
			e._Effects.add(element);
			e._Effects.add(ParserHelper.complement(element.replace("K", "K~")));
			a_human._Effects.add(e);
			domain_translated.list_actions.put(a_human.Name, a_human);
			ArrayList<Action> aList = new ArrayList<>();
			for(String action : domain_translated.list_actions.keySet()){
				Action a = domain_translated.list_actions.get(action);
				if(a.affectedBranches(ParserHelper.complement(element))){
					aList.add(a);
				}
			}
			for(Action a : aList){
				a._Effects.remove(ParserHelper.complement("Knot-started"));
				for(Branch b :a._Branches){
					if(b._Branches.contains(ParserHelper.complement(element))){
						b._Branches.remove("K~not-started");
						b._Branches.remove(ParserHelper.complement("Knot-started"));
						b._Branches.add("Knot-started");
						b._Branches.add(ParserHelper.complement("K~not-started"));
					}else{
						//b._Branches.add("K~not-started");
						//b._Branches.add(ParserHelper.complement("Knot-started"));
					}
				}
			}
		}
	}

	private static void addHumanObservation(Action a, Action a_old, int cost, boolean ontop) {
		Action a_human = new Action();
		a_human.IsObservation = true;
		a_human.Name = a.Name + "_humansensor";
		a_human.cost = cost;
		for(String precondition : a._precond){
			if(precondition.startsWith("Knot-observed-")){
				a_human._precond.add(precondition);
			}
		}
		if(ontop) {
			a_human._precond.add("Knot-started");
		}
		Branch br1 = new Branch();
		br1._Branches.add("K" + a_old._Effects.get(0)._Effects.get(0));
		Branch br2 = new Branch();
		br2._Branches.add("K~" + a_old._Effects.get(0)._Effects.get(0));
		a_human._Branches.add(br1);
		a_human._Branches.add(br2);
		domain_translated.list_actions.put(a_human.Name, a_human);
	}

	private static void addSpecialActions(Problem p, boolean ontop) {
		int cost = 10;
		//boolean deadEndsFound = false;
        //Heuristic h = new Heuristic(p, null, jG, heuristic);
        //Node initNode = new Node(p.getInitState());
        //int hVal = h.getValue(initNode);
        //if(hVal >= Integer.MAX_VALUE || hVal < 0){
			/*BitSet acts = new BitSet();
        	System.out.println("Dead-end!!!! of type 1 or 3");
			addHumanInterventionActions(cost, ontop);
			domain_translated.costFunction = true;
			changes = true;
			*//*for(VAction obs : p.hObservations){
				acts.set(p.insertHumanObservation(obs, cost));
				domain_translated.costFunction = true;
			}*//*
			h = new Heuristic(p, null, jG, heuristic);
			h.useCosts();
			initNode = new Node(p.getInitState());
			hVal = h.getValueI(initNode,acts);
			if(hVal < Integer.MAX_VALUE && hVal >= 0){
				System.out.println("Corrected Problem.");
				System.out.println("Excuse: " + h.getExcuse());
			}
        }else{
			System.out.println("A priori there exists at least a weak solution.");

		}*/
		changes = true;
		addHumanInterventionActions(cost, ontop);
	}

	private static void initDomain(String domain_file_path, String problem_file_path) {
		domain = initParsing(domain_file_path, problem_file_path);
		domain.getMutexFree();
		/*Ground conditional effects*/
		domain.detectInvariants();
		boolean areGrounded = domain.ground_all_actions();
		/*if(!(hidden_file == null)){
			parseHidden(hidden_file);
		}*/
		/*Process entry*/
		if(!areGrounded) {
			domain.getInvariantPredicates();
			domain.eliminateInvalidActions();
			//domain.eliminateInvalidObservations();
			domain.eliminateUselessEffects();
		}
		if(domain.predicates_grounded.isEmpty()){
			HashSet<String> listPredicatesGrounded = new HashSet<String>();
			for(String action : domain.list_actions.keySet()){
				for(String prec : domain.list_actions.get(action)._precond){
					if(!prec.startsWith("~")) listPredicatesGrounded.add(prec);
				}
				for(Effect eff : domain.list_actions.get(action)._Effects){
					for(String effect : eff._Effects){
						if(!effect.startsWith("~")) listPredicatesGrounded.add(effect);
					}
				}
				for(Branch br : domain.list_actions.get(action)._Branches){
					for(String branch : br._Branches){
						if(!branch.startsWith("~")) listPredicatesGrounded.add(branch);
					}
				}
			}
			domain.predicates_grounded.addAll(listPredicatesGrounded);
		}
		//domain.transformToVariables();
		if(!domain.UncertainPredicates.isEmpty()){
			domain.reInitialState();
		}
	}

	private static Translation translate(String type, Domain domain){
		if(type.equals("internal")){
			InternalTranslation it = new InternalTranslation(domain, cg);
			return it;
		}
		if(type.equals("linear")){
			LinearTranslation lt = new LinearTranslation(domain, cg);
			return lt;
		}else if(type.equals("deadend")){
			//TranslateDeadEnd tr = new TranslateDeadEnd(domain, cg);
			TranslatorTag tr = new TranslatorTag(domain);
			return tr;
		}else{
			Translator_Kt tr = new Translator_Kt(domain);
			return tr;
		}
	}
	
	private static void printDomain(Translation tr) {
		tr.getDomainTranslated().hidden_state = domain.hidden_state;
		long startTime = System.currentTimeMillis();
		Printer.print(outputPath + "Kdomain.pddl", outputPath + "Kproblem.pddl", 
				tr.getDomainTranslated(), tr.getListAxioms());
		long endTime = System.currentTimeMillis();
		//System.out.println("Printing time: " + (endTime - startTime) + " Milliseconds");
	}

	public static Domain initParsing(String pathDomain, String pathProblem){
		Parser p = new Parser(pathDomain, pathProblem);
		Domain domain_completed = p.getDomain();
		return domain_completed;
	}
	
	private static void parseHidden(String path){
		Scanner scan;
		try {
			scan = new Scanner(new File(path));
			String content1 = scan.useDelimiter("\\Z").next();
			scan.close();
			domain.addHiddenState(content1);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
	}
	
	@SuppressWarnings("unused")
	public static void callClgPlanner(){
		// Run a java app in a separate system process
		//./clg -a 1 -c 1 -v 1 -k 1 -p ./ -o Kdomain.pddl -f Kproblem.pddl | grep '[0-9][0-9]*:\s'
		//./clg -a 1 -c 1 -v 1 -k 0 -p ./ -o new-d.pddl -f new-p.pddl
		//./clg -a 1 -c 1 -v 1 -k 0 -p ./ -o new-d.pddl -f new-p.pddl
		try {
			//String programName = "./clg";
			String programName = "/home/ignasi/workspace/CLG_cluster/clg";
			String commandA = "-a";
			String commandC = "-c";
			String commandV = "-v";
			String commandK = "-k";
			String valueTrue = "1";
			String valueFalse = "0";
			String commandPath = "-p";
			String path = "./";
			
			String operatorFile = "-o";
			String domainPathFile = "Kdomain.pddl";
			String factFile = "-f";
			String problemPathFile = "Kproblem.pddl";
			
			String[] CMD_ARRAY = { programName, commandA, valueTrue , commandC, 
					valueTrue, commandV, valueTrue, commandK, valueFalse, 
					commandPath, path, operatorFile, domainPathFile, factFile, problemPathFile};
			ProcessBuilder builder = new ProcessBuilder();
			builder.command(CMD_ARRAY);
			// Then retrieve the process output
			builder.redirectOutput(new File("plan.txt"));
			builder.redirectError(new File("plan.txt"));
			//System.out.println("" + builder.command());
			Process p = builder.start();
			InputStream in = p.getInputStream();
			InputStream err = p.getErrorStream();
		    p.waitFor();
		    
		    p.getInputStream().close();
		    p.getOutputStream().close();
		    p.getErrorStream().close();
		    //Store the plan:
			//Readplan();
		    ReadStats();
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}

	private static void ReadStats() {
		try{
			String content1 = new String(Files.readAllBytes(Paths.get("plan.txt")), Charset.defaultCharset());
			Matcher m = Pattern.compile("Total number of actions: ([0-9][0-9]*)").matcher(content1);			
		    while(m.find()) {
		    	String aux = m.group(1).trim();
		    	//getPlan().add(aux);
		    	System.out.println("Plan Size: " + aux);
		    }
		}catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}		
	}

	public static ArrayList<String> getPlan() {
		return _Plan;
	}
	
	public static void setPlan(ArrayList<String> _Plan) {
		Planner._Plan = _Plan;
	}

	public static Hashtable<String, String> getObservationSelected() {
		return _ObservationSelected;
	}

	public static void setObservationSelected(Hashtable<String, String> _ObservationSelected) {
		Planner._ObservationSelected = _ObservationSelected;
	}
}
