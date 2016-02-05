package translating;

import java.util.ArrayList;
import java.util.Hashtable;

import pddlElements.Action;
import pddlElements.Domain;

public abstract class Translation {
	//
	//abstract public Domain domain_translated;
	public abstract Domain getDomainTranslated();
	abstract void translatePredicates(ArrayList<String> predicates_grounded, Hashtable<String, Integer> predicates_invariants_grounded);
	abstract void translateInitialState(Hashtable<String, Integer> state);
	abstract void translateGoal(ArrayList<String> goalState);
	abstract void translateActions(Hashtable<String, Action> list_actions);
}