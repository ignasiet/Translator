package bdd;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.JFactory;

public class BDDUtils {

	BDDFactory bddFactory;
	BDD bdd;

	//TODO values as parameters
	// max 2097151
	private static int nodenum = 5000;
	private static int cachesize = 5000;
	private static int numberVariables = 5000;

	public BDDUtils(){
		bddFactory = JFactory.init(nodenum, cachesize);
		bddFactory.setVarNum(numberVariables); // Set the number of used BDD variables.
	}
	
	public BDD createTrueBDD(int label){
		BDD bdd = bddFactory.ithVar(label);
		return bdd;
	}
	
	public BDD createFalseBDD(int label){
		BDD bdd = bddFactory.nithVar(label);
		return bdd;
	}
	
	public BDD zero(){
		return bddFactory.zero();
	}
	
	public BDD one(){
		return bddFactory.one();
	}

}