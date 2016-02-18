package bdd;

import java.util.ArrayList;

import net.sf.javabdd.BDD;

public class BDDAction {
	
	public BDD preconditions;
	public BDD effects;
	public ArrayList<Integer> modify = new ArrayList<Integer>();
	
	public String Name;
	
	public BDDAction() {
		
	}

	public ArrayList<Integer> getChangeList() {
		return modify;
	}

}
