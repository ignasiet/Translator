package HHCP;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;

import pddlElements.Action;
import pddlElements.Axiom;

/**
 * Created by ignasi on 15/05/17.
 */
public class Node {

    private BitSet State;
    //implement WA*?
    private int w = 2;
    private int h; //Heuristic
    private int g; //Cost
    public Node parent;
    public String parentAction;
    //Index of the parent action
    public int indexAction = -1;
    //Index of the parent effect
    public int indexEffect;
    public ArrayList<Integer> axioms;

    public Node(BitSet state){
        State = (BitSet) state.clone();
    }

    public boolean isApplicable(VAction a){
    	BitSet A = (BitSet) a.preconditions.clone();
    	A.and(State);
        return A.equals(a.preconditions);
    }
    
    /**TODO: optimize this function*/
    public boolean holds(int[] conditions){
        if(conditions == null) return true;
        for(int precondition : conditions){
            if(!State.get(precondition)){
                return false;
            }
        }
        return true;
    }

    public void setCost(int cost) {
        this.g = cost;
    }

    public void setHeuristic(int h) {
        this.h = h;
    }

    public int getH() {
        return h;
    }

    public int getCost() {
        return g;
    }

    public int getFunction() {
        return h + g;
    }

    public BitSet getState() {
        return State;
    }

    public Node applyDeterministicAction(VAction a){
        BitSet successor = (BitSet) State.clone();
        for(VEffect v : a.getEffects()){
            if(holds(v.getCondition())){
                for(int e : v.getDelList()){
                    successor.set(e, false);
                }
                for(int e : v.getAddList()){
                    successor.set(e, true);
                }
            }
        }
        Node n = new Node(successor);
        n.parentAction = a.getName();
        n.indexAction = a.index;
        n.parent = this;
        return n;
    }

    public ArrayList<Node> applyNonDeterministicAction(VAction a, ArrayList<VAction> vAxioms){
        ArrayList<Node> successors = new ArrayList<Node>();
        for(VEffect v : a.getEffects()){
            BitSet successor = (BitSet) State.clone();
            if(holds(v.getCondition())){
                for(int e : v.getDelList()){
                    successor.set(e, false);
                }
                for(int e : v.getAddList()){
                    successor.set(e, true);
                }
            }
            Node n = new Node(successor);
            n.parent = this;
            n.indexAction = a.index;
            n.indexEffect = a.getEffects().indexOf(v);
            n.parentAction = a.getName();
            fixedPoint(n, vAxioms);
            successors.add(n);
        }
        return successors;
    }

	public void fixedPoint(Node n, ArrayList<VAction> vAxioms) {
		n.axioms = new ArrayList<>();
		BitSet oldState = (BitSet) n.getState().clone();
		boolean fix = false;
		while(!fix){
			for(VAction ax : vAxioms){
				BitSet prec = (BitSet) ax.preconditions.clone();
				prec.and(n.getState());
				if(prec.equals(ax.getPreconditions())){
					if(!n.axioms.contains(ax.index)) n.axioms.add(ax.index);
					for(int index : ax.getEffects().get(0).getAddList()){
						n.getState().set(index);
					}
					for(int index : ax.getEffects().get(0).getDelList()){
						n.getState().set(index, false);
					}
				}
			}
			if(oldState.equals(n.getState())) fix = true;
			oldState = (BitSet) n.getState().clone();
		}
	}
}
