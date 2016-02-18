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

		// add options
		options.addOption("h", "help", false, "Show help.");
		options.addOption("on", "online", false, "Performs an online search (default is false)");
		options.addOption("o", "output",  true, "Output folder for translated problems.");
		options.addOption("d", "domain", true, "Domain file.");
		options.addOption("p", "problem", true, "Problem file.");
		options.addOption("r", "hidden", true, "Real World file.");
		options.addOption("t", "trans", true, "Translation.");
		
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
				if(!cmd.hasOption("r")){
					System.out.println("No simulation");
					simulateFlag = false;
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
					default:
						translationType = "ktype";
						break;
					}					
				}
				String domainfile = cmd.getOptionValue("d");
				String problemfile = cmd.getOptionValue("p");
				String outputfile = cmd.getOptionValue("o");
				String hiddenfile = cmd.getOptionValue("r");
				Planner.startPlanner(domainfile, problemfile, hiddenfile, outputfile, translationType);
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
	    }catch (ParseException e) {
	    	// oops, something went wrong
	        System.err.println( "Parsing failed.  Reason: " + e.getMessage() );
			e.printStackTrace();
		}		
	}
	
	private static void help() {
		// This prints out some help
		HelpFormatter formater = new HelpFormatter();
		formater.printHelp("Main", options);
		System.exit(0);
	}
}
	
