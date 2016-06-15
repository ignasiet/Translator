package planner;

import pddlElements.Action;

import java.util.ArrayList;

import pddlElements.Domain;
import pddlElements.Effect;
import pddlElements.Axiom;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

/**
 * Created by ignasi on 28/03/16.
 */
public class RelevanceAnalyser {
    public Hashtable<String, ArrayList<String>> context = new Hashtable<String, ArrayList<String>>();
    private ArrayList<Action> _Actions = new ArrayList<Action>();

    public RelevanceAnalyser(Domain d){
        _Actions = d.action_list;
        for(String goal : d.goalState){
            ArrayList<String> empty = new ArrayList<String>();
            context.put(stripChain(goal), empty);
        }
        for(Action a : d.action_list){
            for(String precond : a._precond){
                ArrayList<String> empty = new ArrayList<String>();
                context.put(stripChain(precond),empty);
            }
        }
        calculateContext();
    }

    private String stripChain(String s){
        if(s.contains("_")){
            return s.substring(0, s.indexOf("_"));
        }else{
            return s;
        }
    }

    private void calculateContext(){
        for(Action a : _Actions){
            for(Effect e : a._Effects){
                for(String effect : e._Effects){
                    ArrayList<String> ant = new ArrayList<String>(e._Condition);
                    if(context.containsKey(effect)){
                        Set<String> hs = new HashSet<>();
                        hs.addAll(ant);
                        hs.addAll(context.get(effect));
                        ant.clear();
                        ant.addAll(hs);
                        context.put(effect, ant);
                    }
                }
            }
        }
    }
}
