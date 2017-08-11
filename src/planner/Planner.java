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
import causalgraph.UncertaintyGraph;
import landmark.Landmarker;
import parser.Parser;
import parser.ParserHelper;
import pddlElements.Action;
import pddlElements.Domain;
import pddlElements.Printer;
import simulator.Simulator;
import translating.*;
import causalgraph.CausalGraph;


public class Planner {
	public static Domain domain = new Domain();
	public static Domain domain_translated = new Domain();
	public static int num_replans = 0;
	public static int actions_executed = 0;
	public static int actions_left = 0;
	private static String outputPath = "";
	private static CausalGraph cg;
	private static ArrayList<String> _Plan = new ArrayList<>();
	private static Hashtable<String, String> _ObservationSelected = new Hashtable<String, String>();
	
	public static void startPlanner(String domain_file_path, String problem_file_path, String hidden_file, String file_out_path, String type){
		/*Define problem*/
		if(!(file_out_path == null)){
			outputPath = file_out_path;
		}
		long startTime = System.currentTimeMillis();
		initDomain(domain_file_path, problem_file_path, hidden_file);
		long endTime = System.currentTimeMillis();
		System.out.println("Preprocessing time: " + (endTime - startTime) + " milliseconds");
		

		/*Time measure: translation*/
		domain = ParserHelper.cleanProblem(domain);
		cg = new CausalGraph(domain);
		HashSet<String> relevants = cg.relevantLiterals(domain.goalState);

		UncertaintyGraph uG = new UncertaintyGraph(domain);
		startTime = System.currentTimeMillis();
		/*Set size of the ksets to 2*/
		//Trapper tp = new Trapper(cg.getLiterals(), domain, cg, 2);
		Translation tr = translate(type, domain);
		//LinearTranslation tr = new LinearTranslation(domain);
		endTime = System.currentTimeMillis();
		System.out.println("Translation time: " + (endTime - startTime) + " Milliseconds");
		domain_translated = tr.getDomainTranslated();
		domain_translated.hidden_state = domain.hidden_state;

		/*Planner: review grounded literals*/
		HHCP.Problem p;
		HHCP.Problem hP;
		if(domain_translated.predicates_grounded.isEmpty()){
			p = new Problem(new ArrayList<String>(domain_translated.predicates_posit.keySet()));
			hP = new Problem(new ArrayList<String>(domain_translated.predicates_posit.keySet()));
		}else{
			p = new Problem(domain_translated.predicates_grounded);
			hP = new Problem(domain_translated.predicates_grounded);
		}
		p.setInitState(domain_translated.state);
		p.setGoalState(domain_translated.goalState);
		hP.setInitState(domain_translated.state);
		hP.setGoalState(domain_translated.goalState);
		p.setActions(domain_translated.list_actions);
		for(String name : domain_translated.list_actions.keySet()){
			Action a = domain_translated.list_actions.get(name);
			if(!a.IsObservation){
				hP.insertAction(a, false);
			}
		}
		hP.setDeterminizedObs(tr.getObsHeuristics());
		p.setAxioms(tr.getListAxioms());
		hP.setAxioms(tr.getListAxioms());

		for(String pred : domain.UncertainPredicates){
			hP.uncertainty.add(hP.getPredicate("K"+pred));
			hP.uncertainty.add(hP.getPredicate("K~"+pred));
		}
		for(String pred : domain.obsPredicates){
			hP.observables.add(hP.getPredicate("K"+pred));
		}

		p.setVectorCosts();
		hP.setVectorCosts();

		System.out.println("Transformation to vectors completed. ");
		//LANDMARKS
		Landmarker l = new Landmarker(domain_translated.state, domain_translated.list_actions, domain_translated.goalState);
		
		computeHeuristic(hP);

		System.out.println("Init Search. ");

		//Simulator sim = new Simulator(null, p.getInitState(), p, hP);
		Searcher search = new Searcher(p, hP, l.getLandmarks());
		//search.GenPlanPairs(p.getInitState());
		
		/*Size measure*/
		//System.out.println(domain.predicates_grounded.size() + " " + tr.domain_translated.predicates_grounded.size());
		/*Print domain*/
		if(!(file_out_path == null)) printDomain(tr);
	}
	
	private static void computeHeuristic(Problem p) {
		//boolean deadEndsFound = false;
        Heuristic h = new Heuristic(p, null);
        Node initNode = new Node(p.getInitState());
        int hVal = h.getValue(initNode);
        if(hVal >= Integer.MAX_VALUE || hVal < 0){
			BitSet acts = new BitSet();
        	System.out.println("Dead-end!!!! of type 1 or 3");
			int cost = 10;
			for(VAction obs : p.hObservations){
				acts.set(p.insertHumanObservation(obs, cost));
			}
			h = new Heuristic(p, null);
			h.useCosts();
			initNode = new Node(p.getInitState());
			hVal = h.getValueI(initNode,acts);
			if(hVal < Integer.MAX_VALUE && hVal >= 0){
				System.out.println("Corrected Problem.");
				System.out.println("Excuse: " + h.getExcuse());
			}
        }
	}

	//TODO: before grounding, extract mutex free variables
	private static void initDomain(String domain_file_path, String problem_file_path, String hidden_file) {
		domain = initParsing(domain_file_path, problem_file_path);
		domain.getMutexFree();
		/*Ground conditional effects*/
		domain.ground_all_actions();
		if(!(hidden_file == null)){
			parseHidden(hidden_file);
		}		
		/*Process entry*/
		domain.getInvariantPredicates();
		domain.eliminateInvalidActions();
		//domain.eliminateInvalidObservations();
		domain.eliminateUselessEffects();
		//domain.transformToVariables();
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

	public static void replan(){
		//Replanning:
		//1- clean current plan:
		_Plan.clear();
		//2- translate again! (updated initial state)
		//Translator_Kt tr = new Translator_Kt(domain);
		//Printer.print(outputPath + "Kdomain.pddl", outputPath + "Kproblem.pddl", domain_translated);
	}
	
	public static int randInt(int min, int max) {
	    // NOTE: Usually this should be a field rather than a method
	    // variable so that it is not re-seeded every call.
	    Random rand = new Random();
	    // nextInt is normally exclusive of the top value,
	    // so add 1 to make it inclusive
	    int randomNum = rand.nextInt((max - min) + 1) + min;
	    return randomNum;
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

	/*private static void Readplan() {
		try {
			//String content1 = readFile("plan.txt", Charset.defaultCharset());
			String content1 = new String(Files.readAllBytes(Paths.get("plan.txt")), Charset.defaultCharset());
			//System.out.println("Actions in plan:");
			//^(http|https|ftp)://.*$
			Matcher m = Pattern.compile("(?m)^([0-9][0-9]*):(.*)$").matcher(content1);			
		    while(m.find()) {
		    	String aux = m.group(2).trim();
		    	getPlan().add(aux);
		    	//System.out.println(aux);
		    }
		    //Read observations selected:
		    //Observation selected after action
		    Matcher obs = Pattern.compile("Observation selected after action (.*):\\n.*\\.\\.\\s(K((N_)?.*))\\(\\)").matcher(content1);			
		    while(obs.find()) {
		    	String act = obs.group(1).trim();
		    	String selected = obs.group(2).trim();
		    	//System.out.println("Action: " + act + " observed: " + selected);
		    	//TODO: using K-predicates beware of regex!
		    	if(selected.startsWith("N_")){
		    		getObservationSelected().put(act.toLowerCase(), "~" + selected.substring(2).toLowerCase());
		    	}else{
		    		getObservationSelected().put(act.toLowerCase(), selected.toLowerCase());
		    	}
		    	getObservationSelected().put(act.toLowerCase(), selected.toLowerCase());
		    }
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}*/

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
