package planner;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import pddlElements.Action;
import pddlElements.Domain;
import pddlElements.Effect;

public class CausalGraph {
	public Hashtable<String, ArrayList<String>> antecessor = new Hashtable<String, ArrayList<String>>();
	public Hashtable<String, ArrayList<String>> sucessors = new Hashtable<String, ArrayList<String>>();
	
	public CausalGraph(Domain d){
		Enumeration<String> e = d.list_actions.keys();
		while(e.hasMoreElements()){
			Action a = d.list_actions.get(e.nextElement().toString());
			extract(a);
		}
		e = antecessor.keys();
		while(e.hasMoreElements()){
			String key = e.nextElement().toString();
			ArrayList<String> list = (ArrayList<String>) antecessor.get(key).clone();
			construct(key, list);
		}
	}

	private void extract(Action a) {
		for(Effect e : a._Effects){
			for(String effect : e._Effects){
				ArrayList<String> list = new ArrayList<String>(a._precond);
				list.addAll(e._Condition);
				if(antecessor.containsKey(effect)){
					//list.addAll(antecessor.get(effect));
					//Remove duplicates
					Set<String> hs = new HashSet<>();
					hs.addAll(list);
					hs.addAll(antecessor.get(effect));
					list.clear();
					list.addAll(hs);
					antecessor.put(effect, list);
				}else{
					antecessor.put(effect, list);
				}
			}
		}
	}
	
	private void construct(String key, ArrayList<String> list){
		for(String s : list){
			if(sucessors.containsKey(s)){
				//Remove duplicates
				Set<String> hs = new HashSet<>();
				hs.addAll(sucessors.get(s));
				ArrayList<String> sucList = new ArrayList<String>();
				hs.add(key);
				sucList.addAll(hs);
				sucessors.put(s, sucList);
			}else{
				ArrayList<String> sucList = new ArrayList<String>();
				sucList.add(key);
				sucessors.put(s, sucList);
			}
		}
	}
	
	public boolean isPossibleDeadEnd(Effect e){
		if(e._Condition.isEmpty()){
			return false;
		}
		for(String effect : e._Effects){
			if(effect.startsWith("~")){
				if(sucessors.containsKey(effect.substring(1)) && !sucessors.containsKey(effect) 
						&& antecessor.containsKey(effect) && !antecessor.containsKey(effect.substring(1))){
					return true;
				}
			}
		}
		return false;
	}
}
