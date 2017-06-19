package HHCP;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
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
    public ArrayList<Integer> relaxedSolution = new ArrayList<Integer>();
    public String preferredAction;


    public void setRelaxedSolution(ArrayList<Integer> relaxedSolution) {
        this.relaxedSolution = relaxedSolution;
    }

    public Node(BitSet state){
        State = (BitSet) state.clone();
    }

    public boolean isApplicable(VAction a){
    	BitSet A = (BitSet) a.preconditions.clone();
    	A.and(State);
        return A.equals(a.preconditions);
    }
    
    /**TODO: optimize this function*/
    public boolean holds(BitSet conditions){
        if(conditions == null) return true;
        BitSet A = (BitSet) conditions.clone();
        A.and(State);
        return A.equals(conditions);
        /*for(int precondition : conditions){
            if(!State.get(precondition)){
                return false;
            }
        }
        return true;*/
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
                for(int i = v.getDelList().nextSetBit(0);i>=0;i=v.getDelList().nextSetBit(i+1)){
                    successor.set(i, false);
                }
                //Add operation between bitsets:
                successor.or(v.getAddList());
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
                for(int i = v.getDelList().nextSetBit(0);i>=0;i=v.getDelList().nextSetBit(i+1)){
                    successor.set(i, false);
                }
                //Add operation between bitsets:
                successor.or(v.getAddList());
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

    public Node applyEffect(VEffect v){
        BitSet successor = (BitSet) State.clone();
        if(holds(v.getCondition())){
            /*for(int e : v.getDelList()){
                successor.set(e, false);
            }*/
            for(int i = v.getDelList().nextSetBit(0);i>=0;i=v.getDelList().nextSetBit(i+1)){
                successor.set(i, false);
            }
            //Add operation between bitsets:
            successor.or(v.getAddList());
        }
        Node n = new Node(successor);
        return n;
    }

    public void fixedPoint(Problem p) {
        axioms = new ArrayList<>();
        BitSet oldState = (BitSet) getState().clone();
        boolean fix = false;
        while(!fix){
            for(VAction ax : p.vAxioms){
                BitSet prec = (BitSet) ax.preconditions.clone();
                prec.and(getState());
                if(prec.equals(ax.getPreconditions())){
                    if(!axioms.contains(ax.index)) axioms.add(ax.index);
                    //Add operation between bitsets:
                    getState().or(ax.getEffects().get(0).getAddList());
                    /*for(int index : ax.getEffects().get(0).getAddList()){
                        getState().set(index);
                        //System.out.println("Adding: " + p.getPredicate(index));
                    }*/
                    /*for(int index : ax.getEffects().get(0).getDelList()){
                        getState().set(index, false);
                        //System.out.println("Deleting: " + p.getPredicate(index));
                    }*/
                    for(int index = ax.getEffects().get(0).getDelList().nextSetBit(0);index>=0;index=ax.getEffects().get(0).getDelList().nextSetBit(index+1)){
                        getState().set(index, false);
                    }
                }
            }
            if(oldState.equals(getState())) fix = true;
            oldState = (BitSet) getState().clone();
        }
    }

    /**Sets preferred action*/
    public void setBestRelaxedAction(String action){
        if(action.contains("#")){
            preferredAction = action.substring(0, action.indexOf("#"));
        }else {
            preferredAction = action;
        }
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
                    //Add operation between bitsets:
                    n.getState().or(ax.getEffects().get(0).getAddList());
					/*for(int index : ax.getEffects().get(0).getAddList()){
						n.getState().set(index);
					}*/
					/*for(int index : ax.getEffects().get(0).getDelList()){
						n.getState().set(index, false);
					}*/
                    for(int index = ax.getEffects().get(0).getDelList().nextSetBit(0);index>=0;index=ax.getEffects().get(0).getDelList().nextSetBit(index+1)){
                        n.getState().set(index, false);
                    }
				}
			}
			if(oldState.equals(n.getState())) fix = true;
			oldState = (BitSet) n.getState().clone();
		}
	}


}
