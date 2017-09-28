package main;
import java.util.ArrayList;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import planner.Planner;


public class Main {
	
	private static boolean simulateFlag = true;
	private static Options options = new Options();
	private static ArrayList<Long> times = new ArrayList<Long>();
	
	@SuppressWarnings("unused")
	public static void main(String[] args){
		// create Options object
		boolean ontop = true;
		long cost = 0l;

		// add options
		options.addOption("h", "help", false, "Show help.");
		//options.addOption("on", "online", false, "Performs an online search (default is false)");
		options.addOption("o", "output",  true, "Output folder for translated problems.");
		options.addOption("d", "domain", true, "Domain file.");
		options.addOption("p", "problem", true, "Problem file.");
		//options.addOption("r", "hidden", true, "Real World file.");
		options.addOption("t", "trans", true, "Translation.");
		options.addOption("c", "correction", true, "Correction actions in any place in the plan.");
		//options.addOption("s", "heuristic", true, "Heuristic used.");
		options.addOption("e", "cost", true, "Cost of a dead-end (Default 400000000000l).");
		options.addOption("a", "algorithm", true, "Selected algorithm (LRTDP or ADDMAXL).");
		
		try {
	        // parse the command line arguments
			CommandLineParser parser = new DefaultParser();
			CommandLine cmd = parser.parse(options, args);
			// get c option value			
			if (cmd.hasOption("h")){
				help();
			}else{
				if(!cmd.hasOption("d") | !cmd.hasOption("p")){
					System.out.println("Incorrect call. See help:");
					help();
				}
				if(!cmd.hasOption("o")){
					System.out.println("No output of files");
				}
				/*if(!cmd.hasOption("r")){
					System.out.println("No simulation");
					simulateFlag = false;
				}*/
				if(!cmd.hasOption("c")){
					System.out.println("Correction actions on top (Default).");
				}else{
					System.out.println("Correction actions on demand.");
					ontop = false;
				}
				String translationType = "ktype";
				if(cmd.hasOption("t")){
					switch(cmd.getOptionValue("t")){
					case "1":
						translationType = "linear";
						break;
					case "2":
						translationType = "deadend";
						break;
					case "3":
						translationType = "ktype";
						break;
					default:
						translationType = "internal";
						break;
					}					
				}else{
					translationType = "linear";
				}
				String algorithm = "";
				if(cmd.hasOption("e")){
					System.out.println("Cost of a dead-end: " + cmd.getOptionValue("e"));
					cost = Long.parseLong(cmd.getOptionValue("e"));
				}else{
					cost = 400000000000l;
					System.out.println("Default cost: " + cost);
				}

				if(cmd.hasOption("a")){
					switch(cmd.getOptionValue("a")){
						case "1":
							algorithm = "lrtdp";
							break;
						case "2":
							algorithm = "addmax";
							break;
						default:
							algorithm = "lrtdp";
							break;
					}
				}else{
					algorithm = "lrtdp";
				}
				System.out.println("Algorithm selected: " + algorithm);

				/*if(cmd.hasOption("s")){
					switch(cmd.getOptionValue("s")){
						case "1":
							heuristicType = "ff";
							break;
						case "2":
							heuristicType = "hmax";
							break;
					}
				}else{
					heuristicType = "ff";
				}*/


				String domainfile = cmd.getOptionValue("d");
				String problemfile = cmd.getOptionValue("p");
				String outputfile = cmd.getOptionValue("o");
				//String hiddenfile = cmd.getOptionValue("r");
				Planner.startPlanner(domainfile, problemfile, outputfile,
						translationType, ontop, "ff", cost, algorithm);
				//Time for the planner:
				//callPlanner();
			}
	    }catch (ParseException e) {
	    	// oops, something went wrong
	        System.err.println( "Parsing failed.  Reason: " + e.getMessage() );
			e.printStackTrace();
		}		
	}
	
	private static void callPlanner(){
		//Time for the planner:
		for(int i = 0; i<10; i++){
			long startTime = System.currentTimeMillis();
			Planner.callClgPlanner();
			long endTime = System.currentTimeMillis();
			long time = endTime - startTime;
			System.out.println("FF processing time-" + i + ": " + time + " milliseconds");
			times.add(time);
		}
		long time =0;
		for(int i = 0; i<10;i++){
			time += times.get(i);
		}
		System.out.println("Average time FF: " + time/10);
	}
	
	private static void help() {
		// This prints out some help
		HelpFormatter formater = new HelpFormatter();
		formater.printHelp("Main", options);
		System.exit(0);
	}
}
	
