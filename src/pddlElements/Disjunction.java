/**
 * 
 */
package pddlElements;

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

	public ArrayList<String> getIterator() {
		return listNodes;
	}
}
