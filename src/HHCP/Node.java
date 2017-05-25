package HHCP;

import java.util.ArrayList;
import java.util.BitSet;

/**
 * Created by ignasi on 15/05/17.
 */
public class Node {

    private BitSet State;
    private int h; //Heuristic
    private int g; //Cost
    public Node parent;
    public String parentAction;
    //Index of the parent action
    public int indexAction = -1;
    //Index of the parent effect
    public int indexEffect;

    public Node(BitSet state){
        State = (BitSet) state.clone();
    }

    public boolean isApplicable(VAction a){
        return holds(a.getPreconditionArray());
    }
    
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

    public ArrayList<Node> applyNonDeterministicAction(VAction a){
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
            successors.add(n);
        }
        return successors;
    }
}
