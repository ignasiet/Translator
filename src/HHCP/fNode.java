package HHCP;

import java.util.*;

/**
 * Created by ignasi on 15/05/17.
 */
public class fNode {

    private BitSet State;
    //implement WA*?
    //private int w = 2;
    private float h; //Heuristic
    private float g; //Cost to that node from root
    public fNode parent;
    public String parentAction;
    //Index of the parent action
    public int indexAction = -1;
    //Index of the parent effect
    public int indexEffect;
    public ArrayList<Integer> axioms = new ArrayList<>();;
    public ArrayList<Integer> relaxedSolution = new ArrayList<Integer>();
    public String preferredAction;
    private int[] factslayer;
    private int[] actionCounter;
    //private int[] actionLayer;
    private BitSet scheduledActions;
    public float value = Float.MAX_VALUE;
    public HashMap<Integer, ArrayList<fNode>> successors = new HashMap<Integer, ArrayList<fNode>>();
    public int greedyAction;
    public HashSet<BitSet> visited;
    public int numberSuccessors;
    public boolean hAction = false;


    public fNode(BitSet state){
        State = (BitSet) state.clone();
    }

    public void addVisited(HashSet<BitSet> visiteds){
        visited = new HashSet<>(visiteds);
    }

    public int[] getFactslayer() {
        return factslayer;
    }

    public int[] getActionCounter() {
        return actionCounter;
    }

    /*public int[] getActionLayer() {
        return actionLayer;
    }*/

    public void setFacts(int[] facts){
        factslayer = Arrays.copyOf(facts,facts.length);
    }

    /*public void setActionLayer(int[] actions){
        actionLayer = Arrays.copyOf(actions,actions.length);
    }*/

    public void setActionCounter(int[] counter){
        actionCounter = Arrays.copyOf(counter,counter.length);
    }

    public void setActionCounterInc(Problem problem){
        actionCounter = new int[problem.getVaList().size()];
        for(int i = State.nextSetBit(0);i>=0;i=State.nextSetBit(i+1)){
            if(problem.prec2Act.containsKey(i)) {
                Integer[] actions = problem.prec2Act.get(i);
                for(int index = 0; index< actions.length;index++) {
                    int actionIndex = actions[index];
                    if (actionIndex < problem.indexAxioms) continue;
                    actionCounter[actionIndex]++;
                }
            }
        }
    }

    public void setRelaxedSolution(ArrayList<Integer> relaxedSolution) {
        this.relaxedSolution = relaxedSolution;
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

    public void setCost(float cost) {
        this.g = cost;
    }

    public void setHeuristic(float h) {
        this.h = h;
    }

    public float getH() {
        return h;
    }

    public float getCost() {
        return g;
    }

    public float getFunction() {
        return h + g;
    }

    public BitSet getState() {
        return State;
    }

    public fNode applyDeterministicAction(VAction a, Problem p){
        BitSet successor = (BitSet) State.clone();
        fNode n = new fNode(successor);
        n.setFacts(getFactslayer());
        //n.setActionLayer(getActionLayer());
        n.setActionCounter(getActionCounter());
        BitSet scheduledActions = new BitSet();

        for(VEffect v : a.getEffects()){
            if(holds(v.getCondition())){
                for(int i = v.getDelList().nextSetBit(0);i>=0;i=v.getDelList().nextSetBit(i+1)){
                    n.getState().set(i, false);
                }
                for(int i = v.getAddList().nextSetBit(0);i>=0;i=v.getAddList().nextSetBit(i+1)){
                    n.getState().set(i);
                    if(n.getFactslayer()[i] > 0){
                        n.getFactslayer()[i] = 0;
                        updateAxiomCounter(i, p, n, scheduledActions);
                        //updateActionCounter(i,p,n,scheduledActions);
                        n.scheduledActions = scheduledActions;
                    }
                    //updateAxiomCounter(i, p, n, scheduledActions);
                }
            }
        }

        n.parentAction = a.getName();
        n.indexAction = a.index;
        n.parent = this;
        return n;
    }

    public ArrayList<fNode> applyNonDeterministicAction(VAction a, Problem p){
        ArrayList<fNode> successors = new ArrayList<fNode>();
        for(VEffect v : a.getEffects()){
            fNode n = applyEffect(v, p);
            n.parent = this;
            n.indexAction = a.index;
            n.indexEffect = a.getEffects().indexOf(v);
            n.parentAction = a.getName();
            successors.add(n);
        }
        return successors;
    }

    public fNode applyEffect(VEffect v, Problem p){
        BitSet successor = (BitSet) State.clone();
        fNode n = new fNode(successor);
        n.setFacts(getFactslayer());
        //n.setActionLayer(getActionLayer());
        n.setActionCounter(getActionCounter());
        BitSet scheduledAxioms = new BitSet();

        if(holds(v.getCondition())){
            for(int i = v.getDelList().nextSetBit(0);i>=0;i=v.getDelList().nextSetBit(i+1)){
                n.getState().set(i, false);
            }            
            for(int i = v.getAddList().nextSetBit(0);i>=0;i=v.getAddList().nextSetBit(i+1)){
                if(n.getState().get(i)) continue;
                n.getState().set(i);
                n.getFactslayer()[i] = 1;
                if(n.getFactslayer()[i] > 0){
                    n.getFactslayer()[i] = 0;
                    updateAxiomCounter(i, p, n, scheduledAxioms);
                }
            }
        }
        applyRules(n, scheduledAxioms, p);
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
                    for(int index = ax.getEffects().get(0).getDelList().nextSetBit(0);index>=0;index=ax.getEffects().get(0).getDelList().nextSetBit(index+1)){
                        getState().set(index, false);
                    }
                }
            }
            if(oldState.equals(getState())) fix = true;
            oldState = (BitSet) getState().clone();
        }
        for(int index : axioms){
            VAction rule = p.getAction(index);
            BitSet added = rule.getEffects().get(0).getAddList();
            for(int a = added.nextSetBit(0);a>=0;a=added.nextSetBit(a+1)){
                System.out.println("Deducted: " + p.getPredicate(a));
            }
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

	public void fixedPoint(fNode n, ArrayList<VAction> vAxioms) {
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
                    for(int index = ax.getEffects().get(0).getDelList().nextSetBit(0);index>=0;index=ax.getEffects().get(0).getDelList().nextSetBit(index+1)){
                        n.getState().set(index, false);
                    }
				}
			}
			if(oldState.equals(n.getState())) fix = true;
			oldState = (BitSet) n.getState().clone();
		}
	}

    private void applyRules(fNode n, BitSet scheduledActions, Problem problem) {
        int layerNumber = 0;
        BitSet oldScheduledActions = new BitSet();
        while(!oldScheduledActions.equals(scheduledActions)){
            oldScheduledActions = (BitSet) scheduledActions.clone();
            scheduledActions.clear();
            //1 Read list of scheduled actions:
            for (int i = oldScheduledActions.nextSetBit(0); i >= 0; i = oldScheduledActions.nextSetBit(i+1)) {
                //2 For every predicate that is in the effect of the action (non-det or det), update facts layer.
                //i represents the index of the action
                VAction a = problem.getAction(i);
                for(VEffect e : a.getEffects()){
                    for(int j = e.getAddList().nextSetBit(0); j >= 0; j = e.getAddList().nextSetBit(j+1)){
                        //i: the action
                        //j: the predicate
                        if(n.getState().get(j)) continue;
                        n.getState().set(j);
                        if(!n.axioms.contains(a.index)) n.axioms.add(a.index);
                        if(n.getState().get(j)){                        	
                            n.getFactslayer()[j] = layerNumber;
                            //3 Update actions whose preconditions have been updated
                            updateAxiomCounter(j, problem, n, scheduledActions);
                        }
                    }
                    for(int j = e.getDelList().nextSetBit(0); j >= 0; j = e.getDelList().nextSetBit(j+1)){
                        n.getState().set(j,false);
                    }
                }
            }
        }
    }

    public void updateAxiomCounter(int predicate, Problem problem, fNode node, BitSet scheduledAxioms){
        if(!problem.prec2Act.containsKey(predicate)) {
            return;
        }
        Integer[] actions = problem.prec2Act.get(predicate);
        for(int index = 0; index< actions.length;index++){
            int actionIndex = actions[index];
            if(actionIndex < problem.indexAxioms) continue;
            node.actionCounter[actionIndex]++;
            if(problem.getVaList().get(actionIndex).getPreconditions().cardinality() == node.actionCounter[actionIndex]){
                scheduledAxioms.set(actionIndex,true);
            }
        }
    }

    public void updateActionCounter(int predicate, Problem problem, fNode node, BitSet scheduledActions){
        if(!problem.prec2Act.containsKey(predicate)) {
            return;
        }
        Integer[] actions = problem.prec2Act.get(predicate);
        for(int index = 0; index< actions.length;index++){
            int actionIndex = actions[index];
            node.actionCounter[actionIndex]++;
            if(actionIndex >= problem.indexAxioms && !problem.humanActions.get(actionIndex)) continue;
            //node.actionCounter[actionIndex]++;
            if(problem.getVaList().get(actionIndex).getPreconditions().cardinality() == node.actionCounter[actionIndex]){
                scheduledActions.set(actionIndex,true);
            }
        }
    }

    public void setScheduledActions(BitSet actions){
        scheduledActions = actions;
    }

    public BitSet getScheduledActions(){
        return scheduledActions;
    }

    public void cleanMemory(){
        axioms.clear();
        relaxedSolution.clear();
        factslayer = null;
        actionCounter = null;
        //actionLayer = null;
    }
}
