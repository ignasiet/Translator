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
    private int[] difficultyLayer;
    //Mapping from layer level -> goals at that level
    private HashMap<Integer, Integer[]> goalMembership = new HashMap<Integer, Integer[]>();
    private HashMap<Integer, Integer[]> addedBy = new HashMap<Integer, Integer[]>();
    private HashSet<Integer> landmarks;
    private int m;
    private BitSet scheduledActions;
    private BitSet scheduledAxioms;
    //Is predicate at i marked true?
    private BitSet goalMarked;
    private int value = 0;
    private HashSet<Integer> disjunctiveLandmarks = new HashSet<Integer>();
    private ArrayList<Integer> relaxedSolution = new ArrayList<Integer>();
    public HashMap<Integer, ArrayList<Integer>> reSolution = new HashMap<Integer, ArrayList<Integer>>();

    public RelaxedGraphH(Problem p, BitSet state, HashSet<Integer> l){
        problem = p;
        factsLayer = new int[p.getSize()];
        //goalMembership = new int[p.getSize()];
        actionCounter = new int[p.getVaList().size()];
        actionLayer = new int[p.getVaList().size()];
        difficultyLayer = new int[p.getVaList().size()];
        Arrays.fill(factsLayer, Integer.MAX_VALUE);
        goalMarked = new BitSet();
        disjunctiveLandmarks = new HashSet<>(problem.getDisjunctions(state));
        initLayers(state);
        if(l != null) {
            landmarks = l;
        }else{
            landmarks = new HashSet<>();
        }
        if(!landmarks.isEmpty()){
            for(Integer landmark : landmarks){
                expandGraph(landmark);
                if(value==0){
                    BitSet bsGoal = new BitSet();
                    bsGoal.set(landmark);
                    extractPlan(bsGoal);
                    value = relaxedSolution.size();
                }
            }
        }else {
            expandGraph();
            if (value == 0) {
                extractPlan(problem.getGoal());
                value = relaxedSolution.size();
            }
        }

    }

    private void initLayers(BitSet state) {
        //1 Init list of scheduled actions: no action scheduled
        scheduledActions = new BitSet();
        scheduledAxioms = new BitSet();
        //2 For every predicate that is in the current state, update facts layer to put a 0 value
        for (int i = state.nextSetBit(0); i >= 0; i = state.nextSetBit(i+1)) {
            //System.out.println("Predicate: " + i + " correspond to: " + problem.getPredicate(i));
            factsLayer[i] =0;
            //3 Update actions whose preconditions have been updated
            updateActionCounter(i,0);
        }
    }

    /**Expand the graph until a solution has been found*/
    private void expandGraph(){
        //0 Init layer number = 1 (0 is the initial layer)
        int layerNumber = 0;
        BitSet oldScheduledActions = new BitSet();
        while(!goalReached() && !(oldScheduledActions.equals(scheduledActions))){
            layerNumber++;
            oldScheduledActions = (BitSet) scheduledActions.clone();
            scheduledActions.clear();
            Hashtable<Integer, BitSet> DeductedPredicates = new Hashtable<Integer, BitSet>();
            //1 Read list of scheduled actions:
            for (int i = oldScheduledActions.nextSetBit(0); i >= 0; i = oldScheduledActions.nextSetBit(i+1)) {
                //2 For every predicate that is in the effect of the action (non-det or det), update facts layer.
                //i represents the index of the action
                VAction a = problem.getAction(i);
                if(a.isObservation){
                    //Treat effects separately and then merge the results
                    //Bitsets for controlling which axioms to fire
                    BitSet noAxioms = new BitSet();
                    for(VEffect e : a.getEffects()){
                        //Bitsets for controlling which axioms to fire
                        BitSet addedPredicates = new BitSet();
                        BitSet forbidenAxioms = new BitSet();
                        //We must not fire axioms activated with other predicates
                        int[] axiomCounter = Arrays.copyOf(actionCounter, actionCounter.length);
                        //The first update is the effect of the observation:
                        performNonDetUpdates(e, layerNumber, addedPredicates, forbidenAxioms, noAxioms, axiomCounter);
                        HashSet<Integer> applied = new HashSet<Integer>();
                        //Obtain what can be fired
                        fixedPointAxiomsComputation(applied, addedPredicates, layerNumber, forbidenAxioms, noAxioms, axiomCounter);
                        //Here we must clean what was added by the older outcome of the observation
                        cleanAddedAxioms(DeductedPredicates, i, addedPredicates);
                        noAxioms.or(forbidenAxioms);
                        forbidenAxioms.clear();
                    }
                }else{
                    performUpdates(a, i, layerNumber);
                }
            }
            //Here we must update all added predicates (in the same layer)!
            updateAfterAxioms(DeductedPredicates, layerNumber);
        }
        if(goalReached()){
            m=layerNumber;
        }else{
            //Not solution
            value = Integer.MAX_VALUE;
        }
    }

    /**Expand the graph until a solution has been found*/
    private void expandGraph(HashSet<Integer> landmarks){
        //0 Init layer number = 1 (0 is the initial layer)
        int layerNumber = 0;
        BitSet oldScheduledActions = new BitSet();
        while(!goalReached() && !landmarksReached(landmarks) && !(oldScheduledActions.equals(scheduledActions))){
            layerNumber++;
            oldScheduledActions = (BitSet) scheduledActions.clone();
            scheduledActions.clear();
            Hashtable<Integer, BitSet> DeductedPredicates = new Hashtable<Integer, BitSet>();
            //1 Read list of scheduled actions:
            for (int i = oldScheduledActions.nextSetBit(0); i >= 0; i = oldScheduledActions.nextSetBit(i+1)) {
                //2 For every predicate that is in the effect of the action (non-det or det), update facts layer.
                //i represents the index of the action
                VAction a = problem.getAction(i);
                if(a.isObservation){
                    //Treat effects separately and then merge the results
                    //Bitsets for controlling which axioms to fire
                    BitSet noAxioms = new BitSet();
                    for(VEffect e : a.getEffects()){
                        //Bitsets for controlling which axioms to fire
                        BitSet addedPredicates = new BitSet();
                        BitSet forbidenAxioms = new BitSet();
                        //We must not fire axioms activated with other predicates
                        int[] axiomCounter = Arrays.copyOf(actionCounter, actionCounter.length);
                        //The first update is the effect of the observation:
                        performNonDetUpdates(e, layerNumber, addedPredicates, forbidenAxioms, noAxioms, axiomCounter);
                        HashSet<Integer> applied = new HashSet<Integer>();
                        //Obtain what can be fired
                        fixedPointAxiomsComputation(applied, addedPredicates, layerNumber, forbidenAxioms, noAxioms, axiomCounter);
                        //Here we must clean what was added by the older outcome of the observation
                        cleanAddedAxioms(DeductedPredicates, i, addedPredicates);
                        noAxioms.or(forbidenAxioms);
                        forbidenAxioms.clear();
                    }
                }else{
                    performUpdates(a, i, layerNumber);
                }
            }
            //Here we must update all added predicates (in the same layer)!
            updateAfterAxioms(DeductedPredicates, layerNumber);
        }
        if(!landmarksReached(landmarks) && !goalReached()){
            value = Integer.MAX_VALUE;
        }
        m=layerNumber;
    }

    private void fixedPointAxiomsComputation(HashSet<Integer> applied, BitSet addedPredicates, int layerNumber, BitSet forbidenAxioms, BitSet noAxioms, int[] axiomCounter) {
        boolean fix = false;
        //In this fixed point we should get all the fired axioms
        while(!fix){
            BitSet oldScheduledAxioms = (BitSet) scheduledAxioms.clone();
            for (int axIndex = oldScheduledAxioms.nextSetBit(0); axIndex >= 0;
                 axIndex = oldScheduledAxioms.nextSetBit(axIndex+1)) {
                //Get the index of the axiom and apply it
                if(!applied.contains(axIndex) && !uselessAxiom(axIndex, addedPredicates)) {
                    applied.add(axIndex);
                    VAction axiom = problem.getAction(axIndex);
                    //The predicates are added by the observation not the axioms!
                    performNonDetUpdates(axiom.getEffects().get(0), layerNumber, addedPredicates,forbidenAxioms, noAxioms, axiomCounter);
                }
            }
            if(oldScheduledAxioms.equals(scheduledAxioms)) fix = true;
        }
    }

    /**Return if an axiom is useless, i.e. all its information is known*/
    private boolean uselessAxiom(int axIndex, BitSet addedPredicates) {
        BitSet effs = problem.getAction(axIndex).getEffects().get(0).getAddList();
        for(int i =effs.nextSetBit(0);i>=0;i=effs.nextSetBit(i+1)){
            if(!addedPredicates.get(i)){
                return false;
            }
        }
        return true;
    }

    private void cleanAddedAxioms(Hashtable<Integer, BitSet> deductedPredicates, int action, BitSet addedPredicates) {
        if(deductedPredicates.containsKey(action)){
            BitSet bS = (BitSet) addedPredicates.clone();
            bS.or(deductedPredicates.get(action));
            deductedPredicates.put(action, bS);
        }else{
            BitSet bS = (BitSet) addedPredicates.clone();
            deductedPredicates.put(action, bS);
        }
        scheduledAxioms.clear();
    }

    /**Updates the actions counters and the scheduled actions*/
    private void performUpdates(VAction a, int actionIndex, int layerNumber){
        for(VEffect e : a.getEffects()){
            for(int j = e.getAddList().nextSetBit(0); j >= 0; j = e.getAddList().nextSetBit(j+1)){
                //actionIndex: the action
                //j: the predicate
                addRelation(j, actionIndex);
                if(factsLayer[j] > layerNumber){
                    factsLayer[j] = layerNumber;
                    //3 Update actions whose preconditions have been updated
                    updateActionCounter(j, layerNumber);
                }
            }
        }
    }

    /**Updates the non deterministic effects of actions */
    private void performNonDetUpdates(VEffect e, int layerNumber, BitSet addedPredicates, BitSet forbidenAxioms, BitSet noAxioms, int[] axiomsCounter){
        for(int j = e.getAddList().nextSetBit(0); j >= 0; j = e.getAddList().nextSetBit(j+1)){
            //actionIndex: the action
            //j: the predicate
            if(factsLayer[j] > layerNumber){
                //factsLayer[j] = layerNumber;
                if(!addedPredicates.get(j)) {
                    addedPredicates.set(j);
                    //3 Update actions whose preconditions have been updated
                    updateAxiomsCounter(j, forbidenAxioms, noAxioms, axiomsCounter);
                }
            }
        }
    }

    private void updateAfterAxioms(Hashtable<Integer, BitSet> effects, int layerNumber){
        for(int action : effects.keySet()){
            for(int j = effects.get(action).nextSetBit(0); j >= 0; j = effects.get(action).nextSetBit(j+1)){
                //actionIndex: the action
                //j: the predicate
                //if(!disjunctiveLandmarks.contains(j)) continue;
                addRelation(j, action);
                if(factsLayer[j] > layerNumber){
                    factsLayer[j] = layerNumber;
                    //3 Update actions whose preconditions have been updated
                    updateActionCounter(j, layerNumber);
                }
            }
        }
        effects.clear();
    }

    /**Expand the graph until a landmark has been found*/
    private void expandGraph(Integer landmark){
        //0 Init layer number = 1 (0 is the initial layer)
        int layerNumber = 0;
        BitSet oldScheduledActions = new BitSet();
        while(!landmarkReached(landmark) && !(oldScheduledActions.equals(scheduledActions))){
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
        if(!landmarkReached(landmark)){
            value = Integer.MAX_VALUE;
        }
        m=layerNumber;
    }

    private void addRelation(int predicate, int action) {
        if(addedBy.containsKey(predicate)){
            Integer[] oldList = addedBy.get(predicate);
            Integer[] newList = Arrays.copyOf(oldList, oldList.length + 1);
            newList[oldList.length] = action;
            Arrays.sort(newList, new MyComparator());
            addedBy.put(predicate, newList);
        }else{
            Integer[] listNew = new Integer[1];
            listNew[0] = action;
            addedBy.put(predicate, listNew);
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

    private void extractPlan(BitSet goal){
        //for(int i = 0;i<problem.getGoal().length;i++){
        for(int i = goal.nextSetBit(0);i >= 0; i = goal.nextSetBit(i+1)){
            //Do I need this? test and see...
            addList(m, i, goalMembership);
        }
        HashSet<Integer> solved = new HashSet<Integer>();
        for(int i = m; i>0; i--){
            //Get the goals of level m
            if(goalMembership.containsKey(i)) {
                Integer[] goals = goalMembership.get(i);
                ArrayList<Integer> goalsLowerLayer = new ArrayList<Integer>();
                for (int g : goals) {
                    if (solved.contains(g) || (factsLayer[g] == 0)) continue;
                    //Obtain the minimal difficulty action and add it to the relaxed solution
                    Integer minAct = addedBy.get(g)[0];
                    solved.add(g);
                    if (!relaxedSolution.contains(minAct)) relaxedSolution.add(minAct);
                    layerSolution(actionLayer[minAct], minAct);
                    //Add its preconditions to the goal of lower layers
                    //WARNING: only if not marked true already!
                    //TODO: if the fact is added after, then choose another fact
                    VAction a = problem.getAction(minAct);
                    for (int pr = a.preconditions.nextSetBit(0); pr >= 0; pr = a.preconditions.nextSetBit(pr + 1)) {
                        if ((factsLayer[pr] == 0) || goalsLowerLayer.contains(pr)) continue;
                        if (!(factsLayer[pr] >= i)) {
                            addGoalMembership(pr);
                            //goalsLowerLayer.add(pr);
                        }
                    }
                    //Mark other effects true
                    for (VEffect e : a.getEffects()) {
                        if (e.getAddList().get(g)) {
                            for (int j = e.getAddList().nextSetBit(0); j >= 0; j = e.getAddList().nextSetBit(j + 1)) {
                                if (factsLayer[j] >= i) solved.add(j);
                            }
                        }
                    }
                }
            }
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

    private void layerSolution(int level, int action){
        if(!reSolution.containsKey(level)){
            ArrayList<Integer> l = new ArrayList<Integer>();
            l.add(action);
            reSolution.put(level, l);
        }else{
            ArrayList<Integer> l = new ArrayList<Integer>(reSolution.get(level));
            l.add(action);
            reSolution.put(level, l);
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
                if(actionIndex < problem.indexAxioms) {
                    scheduledActions.set(actionIndex, true);
                }
                /*else{
                    scheduledAxioms.set(actionIndex, true);
                }*/
            }else{

            }
        }
    }

    private void updateAxiomsCounter(int predicate, BitSet forbidenAxioms, BitSet noAxiom, int[] counter) {
        if(!problem.prec2Act.containsKey(predicate)) {
            return;
        }
        //TODO: what to do with an axiom that has been fired?
        Integer[] actions = problem.prec2Act.get(predicate);
        for(int index = 0; index< actions.length;index++){
            int actionIndex = actions[index];
            if(noAxiom.get(actionIndex)){
                continue;
            }
            counter[actionIndex]++;
            forbidenAxioms.set(actionIndex);
            //difficultyLayer[actionIndex] += layer;
            //4 if size preconditions == action layer size, schedule action
            if(counter[actionIndex] >= problem.getAction(actionIndex).getPreconditions().cardinality()){
                counter[actionIndex] = problem.getAction(actionIndex).getPreconditions().cardinality();
                //actionLayer[actionIndex] = layer;
                if(actionIndex >= problem.indexAxioms){
                    scheduledAxioms.set(actionIndex, true);
                }
            }
        }
    }

    private boolean goalReached(){
        for(int i=problem.getGoal().nextSetBit(0);i>=0;i = problem.getGoal().nextSetBit(i+1)){
            if(factsLayer[i] == Integer.MAX_VALUE){
                return false;
            }
        }
        return true;
    }

    private boolean landmarkReached(Integer i){
        if(factsLayer[i] == Integer.MAX_VALUE){
            return false;
        }
        return true;
    }

    private boolean landmarksReached(HashSet<Integer> hs){
        for(Integer index : hs){
            if(factsLayer[index] < Integer.MAX_VALUE){
                return true;
            }
        }
        return false;
    }

    private int obtainLandmarksReached(HashSet<Integer> hs){
        for(Integer index : hs){
            if(factsLayer[index] < Integer.MAX_VALUE){
                return index;
            }
        }
        return -1;
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

