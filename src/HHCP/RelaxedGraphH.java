package HHCP;

import java.util.*;

/**
 * Created by ignasi on 16/05/17.
 */
public class RelaxedGraphH {

    private Problem problem;
    private int[] factsLayer;
    private int[] actionCounter;
    private int[] actionLayer;
    private int[] axiomLayer;
    private int[] difficultyLayer;
    //Mapping from layer level -> goals at that level
    private HashMap<Integer, Integer[]> goalMembership = new HashMap<Integer, Integer[]>();
    private HashMap<Integer, Integer[]> addedBy = new HashMap<Integer, Integer[]>();
    private int m;
    private BitSet scheduledActions;
    //Is predicate at i marked true?
    private BitSet goalMarked;
    private int value = 0;
    private ArrayList<Integer> relaxedSolution = new ArrayList<Integer>();

    public RelaxedGraphH(Problem p, BitSet state){
        problem = p;
        factsLayer = new int[p.getSize()];
        //goalMembership = new int[p.getSize()];
        actionCounter = new int[p.getVaList().size()];
        actionLayer = new int[p.getVaList().size()];
        difficultyLayer = new int[p.getVaList().size()];
        Arrays.fill(factsLayer, Integer.MAX_VALUE);
        //Arrays.fill(difficultyLayer, Integer.MAX_VALUE);
        //Arrays.fill(actionCounter, Integer.MIN_VALUE);
        goalMarked = new BitSet();
        initLayers(state);
        expandGraph();
        if(value==0){
            extractPlan();
            value = relaxedSolution.size();
        }
    }

    private void initLayers(BitSet state) {
        //1 Init list of scheduled actions: no action scheduled
        scheduledActions = new BitSet();
        //scheduledActions = new BitSet(problem.getVaList().size());
        //2 For every predicate that is in the current state, update facts layer to put a 0 value
        for (int i = state.nextSetBit(0); i >= 0; i = state.nextSetBit(i+1)) {
            //System.out.println("Predicate: " + i + " correspond to: " + problem.getPredicate(i));
            factsLayer[i] =0;
            //3 Update actions whose preconditions have been updated
            updateActionCounter(i,0);
        }
    }

    private void expandGraph(){
        //0 Init layer number = 1 (0 is the initial layer)
        int layerNumber = 0;
        BitSet oldScheduledActions = new BitSet();
        while(!goalReached() && !(oldScheduledActions.equals(scheduledActions))){
            layerNumber++;
            oldScheduledActions = (BitSet) scheduledActions.clone();
            scheduledActions.clear();
            //1 Read list of scheduled actions:
            for (int i = oldScheduledActions.nextSetBit(0); i >= 0; i = oldScheduledActions.nextSetBit(i+1)) {
                //2 For every predicate that is in the effect of the action (non-det or det), update facts layer.
                //i represents the index of the action
                VAction a = problem.getAction(i);
                /*if(i >= problem.indexAxioms){
                    axiomLayer[i] = layerNumber;
                    fixedPointAxioms(layerNumber, i);
                }*/
                for(VEffect e : a.getEffects()){
                    for(int j = e.getAddList().nextSetBit(0); j >= 0; j = e.getAddList().nextSetBit(j+1)){
                        //i: the action
                        //j: the predicate
                        addRelation(j, i);
                        if(factsLayer[j] > layerNumber){
                            factsLayer[j] = layerNumber;
                            //3 Update actions whose preconditions have been updated
                            updateActionCounter(j, layerNumber);
                        }
                    }
                }
            }
        }
        //System.out.println("Relaxed graph expanded.");
        if(!goalReached()){
            value = Integer.MAX_VALUE;
        }
        m=layerNumber;
    }

    //Let us try with the fixed point to the axioms
    private void fixedPointAxioms(int layerNumber, int action){
        boolean fix = false;
        while(!fix){
            VAction ax = problem.getAction(action);
            for(VEffect e : ax.getEffects()){
                for(int j = e.getAddList().nextSetBit(0); j >= 0; j = e.getAddList().nextSetBit(j+1)){
                    addRelation(ax.index, j);
                    if(factsLayer[j] > layerNumber){
                        factsLayer[j] = layerNumber;
                        //3 Update actions whose preconditions have been updated
                        updateActionCounter(j, layerNumber);
                    }
                }
            }
        }
    }

    private void addRelation(int index, int i) {
        if(addedBy.containsKey(index)){
            Integer[] oldList = addedBy.get(index);
            Integer[] newList = Arrays.copyOf(oldList, oldList.length + 1);
            newList[oldList.length] = i;
            Arrays.sort(newList, new MyComparator());
            addedBy.put(index, newList);
        }else{
            Integer[] listNew = new Integer[1];
            listNew[0] = i;
            addedBy.put(index, listNew);
        }
    }

    private void addList(int key, int newValue, HashMap<Integer, Integer[]> map) {
        if(map.containsKey(key)){
            Integer[] oldList = map.get(key);
            Integer[] newList = Arrays.copyOf(oldList, oldList.length + 1);
            newList[oldList.length] = newValue;
            map.put(key, newList);
        }else{
            Integer[] listNew = new Integer[1];
            listNew[0] = newValue;
            map.put(key, listNew);
        }
    }

    private void extractPlan(){
        //for(int i = 0;i<problem.getGoal().length;i++){
        for(int i = problem.getGoal().nextSetBit(0);i >= 0; i = problem.getGoal().nextSetBit(i+1)){
            //Do I need this? test and see...
            addList(m, i, goalMembership);
        }
        HashSet<Integer> solved = new HashSet<Integer>();
        for(int i = m; i>0; i--){
            //Get the goals of level m
            Integer[] goals = goalMembership.get(i);
            ArrayList<Integer> goalsLowerLayer = new ArrayList<Integer>();
            for(int g : goals){
                if(solved.contains(g) || (factsLayer[g] == 0)) continue;
                //Obtain the minimal difficulty action and add it to the relaxed solution
                Integer minAct = addedBy.get(g)[0];
                solved.add(g);
                if(!relaxedSolution.contains(minAct)) relaxedSolution.add(minAct);
                //Add its preconditions to the goal of lower layers
                //WARNING: only if not marked true already!
                //TODO: if the fact is added after, then choose another fact
                VAction a = problem.getAction(minAct);
                for (int pr = a.preconditions.nextSetBit(0); pr >= 0; pr = a.preconditions.nextSetBit(pr+1)) {
                    if((factsLayer[pr] == 0) || goalsLowerLayer.contains(pr))continue;
                    if(!(factsLayer[pr] >= i)){
                        addGoalMembership(pr);
                        //goalsLowerLayer.add(pr);
                    }
                }
                //Mark other effects true
                for(VEffect e : a.getEffects()) {
                    if(e.getAddList().get(g)){
                        for (int j = e.getAddList().nextSetBit(0); j >= 0; j = e.getAddList().nextSetBit(j + 1)) {
                            if(factsLayer[j] >= i)  solved.add(j);
                        }
                    }
                }
            }

            /*if(i>0) {
                goalMembership.put(i-1, goalsLowerLayer.toArray(new Integer[goalsLowerLayer.size()]));
            }*/
        }
    }

    private void addGoalMembership(int pr) {
        int i = factsLayer[pr];
        if(!goalMembership.containsKey(i)){
            Integer[] l = new Integer[1];
            l[0] = pr;
            goalMembership.put(i, l);
        }else{
            Integer[] l = Arrays.copyOf(goalMembership.get(i), goalMembership.get(i).length+1);
            l[goalMembership.get(i).length] = pr;
            goalMembership.put(i, l);
        }
    }

    private void updateActionCounter(int i, int layer){
        if(!problem.prec2Act.containsKey(i)) {
            return;
        }
        Integer[] actions = problem.prec2Act.get(i);
        for(int index = 0; index< actions.length;index++){
            int actionIndex = actions[index];
            actionCounter[actionIndex]++;
            difficultyLayer[actionIndex] += layer;
            //4 if size preconditions == action layer size, schedule action
            if(problem.getVaList().get(actionIndex).getPreconditions().cardinality() == actionCounter[actionIndex]){
                actionLayer[actionIndex] = layer;
                scheduledActions.set(actionIndex,true);
            }
        }
    }

    private boolean goalReached(){
        //int[] goal = problem.getGoal();
        //for(int i=problem.getGoal().nextSetBit(0);i>= goal.length;i++){
        for(int i=problem.getGoal().nextSetBit(0);i>=0;i = problem.getGoal().nextSetBit(i+1)){
            if(factsLayer[i] == Integer.MAX_VALUE){
                return false;
            }
        }
        return true;
    }

    /**Comparator of the difficulty of the actions*/
    public class MyComparator implements Comparator<Integer> {
        @Override
        public int compare(Integer i1, Integer i2) {
            int compare = (actionLayer[i1] > actionLayer[i2]) ? 1 : 0;
            if(compare == 0){
                compare = (actionLayer[i1] == actionLayer[i2]) ? 0 : -1;
            }
            return compare;
        }
    }

    public int getValue(){
        return value;
    }

    public ArrayList<Integer> getRelaxedSolution(){
        return relaxedSolution;
    }
}

