package pddlElements;

import parser.ParserHelper;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;


/**
 * @author ignasi
 *
 */
public class Disjunction {

	private Hashtable<String,Integer> _Tags = new Hashtable<String,Integer>();
	private ArrayList<String> listNodes = new ArrayList<String>();
	private String fluent = "";
	public HashSet<String> derivates = new HashSet<String>();
	public ArrayList<ArrayList<String>> axioms = new ArrayList<ArrayList<String>>();
	public Hashtable<String, ArrayList<String>> variablesDerivates = new Hashtable<String, ArrayList<String>>();

	public void add(String predicate){
		setFluent(predicate);
		if(!_Tags.contains(predicate)){
			_Tags.put(predicate, 1);
			listNodes.add(predicate);
		}
	}

	private void setFluent(String predicate){
		if(fluent.isEmpty()){
			if(predicate.contains("_")){
				fluent = predicate.substring(0, predicate.indexOf("_"));
			}else{
				fluent = predicate;
			}
		}
	}

	public String getFluent(){
		return fluent;
	}

	public boolean hasInside(String predicate){
		return predicate.equals(fluent);
	}

	public boolean contains(String predicate){
		return _Tags.containsKey(predicate);
	}

	public boolean violates(ArrayList<String> predicates){
		ArrayList<String> tags = new ArrayList<String>();
		int counter = 0;
		for(String p : predicates){
			if(contains(p.replace("~", "")) && !tags.contains(p.replace("~", ""))){
				tags.add(p.replace("~", ""));
				if(p.startsWith("~")) counter++;
			}
		}
		if(tags.containsAll(listNodes)) {
			if(counter==0 || counter == listNodes.size()) return true;
		}
		return false;
	}

	public void extractVars(String pred, ArrayList<String> axiom){
		ArrayList<String> cleanedAx = new ArrayList<>();
		for(String a : axiom){
			if(!pred.equals(a)) cleanedAx.add(ParserHelper.complement(a));
		}
		if(variablesDerivates.containsKey(pred)){
			cleanedAx.addAll(variablesDerivates.get(pred));
			variablesDerivates.put(pred, cleanedAx);
		}else {
			variablesDerivates.put(pred, cleanedAx);
		}
	}

	public ArrayList<String> getIterator() {
		return listNodes;
	}
}
