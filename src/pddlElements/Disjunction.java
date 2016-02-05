/**
 * 
 */
package pddlElements;

import java.util.ArrayList;
import java.util.Hashtable;


/**
 * @author ignasi
 *
 */
public class Disjunction {

	private Hashtable<String,Integer> _Tags = new Hashtable<String,Integer>();
	private ArrayList<String> listNodes = new ArrayList<String>();
	private String fluent = "";
	
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
	
	public boolean hasInside(String predicate){
		return predicate.equals(fluent);
	}
	
	public boolean contains(String predicate){
		return _Tags.containsKey(predicate);
	}

	public ArrayList<String> getIterator() {
		return listNodes;
	}
}
