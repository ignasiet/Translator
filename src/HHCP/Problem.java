package HHCP;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import pddlElements.Action;
import pddlElements.Axiom;
import pddlElements.Branch;
import pddlElements.Effect;

import java.lang.reflect.Array;
import java.util.*;

/**
 * Created by ignasi on 15/05/17.
 */
public class Problem {

    private BiMap<Integer, String> Predicates;

    private BitSet initState;
    private BitSet humanActions = new BitSet();
    private BitSet actionsUsed = new BitSet();
    //private BitSet goalSet;
    //private int[] goal;
    private BitSet goal = new BitSet();
    public Hashtable<Integer, Integer[]> prec2Act = new Hashtable<Integer, Integer[]>();
    public Hashtable<String, Integer> actionsIndex = new Hashtable<String, Integer>();
    private ArrayList<VAction> vaList = new ArrayList<VAction>();
    public ArrayList<VAction> vAxioms = new ArrayList<VAction>();
    public ArrayList<VAction> hObservations = new ArrayList<VAction>();
    public HashSet<Integer> uncertainty = new HashSet<Integer>();
    public HashSet<Integer> observables = new HashSet<Integer>();
    public int[] cost;
    public int indexAxioms = 0;
    private int size;

    public Problem(ArrayList<String> predicates) {
        Predicates = HashBiMap.create();
        size = predicates.size();
        //initState = new BitSet(size);
        initState = new BitSet();
        //goalSet = new BitSet();
        int i = 0;
        for(String predicate : predicates){
            Predicates.put(i, predicate);
            i++;
        }
    }

    public int getSize() {
        return size;
    }

    public void setInitState(Hashtable<String, Integer> state){
        for(String predicate : new ArrayList<String>(state.keySet())){
            initState.set(Predicates.inverse().get(predicate),true);
        }
    }

    public void setGoalState(ArrayList<String> goalState){
        //goal = new int[goalState.size()];
        //int i = 0;
        for(String s : goalState){
            //goal[i] = Predicates.inverse().get(s);
            goal.set(Predicates.inverse().get(s));
            //i++;
        }
    }

    public String getPredicate(int index){
        return Predicates.get(index);
    }

    public int getPredicate(String name){
        return Predicates.inverse().get(name);
    }

    public BitSet getGoal() {
        return goal;
    }

    public VEffect createEffects(Effect e){
        VEffect v = new VEffect();
        BitSet cond = new BitSet();
        for(String condition : e._Condition){
            cond.set(Predicates.inverse().get(condition));
        }
        v.setCondition(cond);
        BitSet add = new BitSet();
        BitSet del = new BitSet();
        for(String effect : e._Effects){
            if(effect.startsWith("~")){
                del.set(Predicates.inverse().get(effect.substring(1)));
            }else{
                add.set(Predicates.inverse().get(effect));
            }
        }
        v.setAddList(add);
        v.setDelList(del);
        return v;
    }

    private VEffect createEffectFromList(ArrayList<String> list){
        VEffect v = new VEffect();
        BitSet add = new BitSet();
        BitSet del = new BitSet();
        for(String effect : list){
            if(effect.startsWith("~")){
                del.set(Predicates.inverse().get(effect.substring(1)));
            }else{
                add.set(Predicates.inverse().get(effect));
            }
        }
        v.setAddList(add);
        v.setDelList(del);
        return v;
    }

    public ArrayList<VEffect> createNondeterministicEffects(Effect e, Action a){
        ArrayList<VEffect> listV = new ArrayList<VEffect>();
        //int[] cond = new int[e._Condition.size()];
        BitSet cond = new BitSet();
        int i = 0;
        for(String condition : e._Condition){
            //cond[i] = Predicates.inverse().get(condition);
            cond.set(Predicates.inverse().get(condition));
            i++;
        }
        //Effects
        ArrayList<Integer> addList = new ArrayList<Integer>();
        //BitSet addList = new BitSet();
        ArrayList<Integer> delList = new ArrayList<Integer>();
        for(String effect : e._Effects){
            if(effect.startsWith("~")){
                delList.add(Predicates.inverse().get(effect.substring(1)));
            }else{
                addList.add(Predicates.inverse().get(effect));
                //addList.set(Predicates.inverse().get(effect));
            }
        }
        for(Branch b : a._Branches){
            VEffect v = new VEffect();
            v.setCondition(cond);
            ArrayList<Integer> addBranch = new ArrayList<Integer>();
            //BitSet addBranch = new BitSet();
            ArrayList<Integer> delBranch = new ArrayList<Integer>();
            for(String bnondet : b._Branches){
                if(bnondet.startsWith("~")){
                    delBranch.add(Predicates.inverse().get(bnondet.substring(1)));
                }else{
                    //addBranch.set(Predicates.inverse().get(bnondet));
                    addBranch.add(Predicates.inverse().get(bnondet));
                }
            }
            addBranch.addAll(addList);
            delBranch.addAll(delList);
            //int[] add = new int[addBranch.size()];
            //BitSet addList = new BitSet();
            BitSet add = new BitSet();
            BitSet del = new BitSet();
            //int[] del = new int[delBranch.size()];
            //i = 0;
            for(Integer in : addBranch){
                //add[i] = in;
                //i++;
                add.set(in);
            }
            //i = 0;
            for(Integer in : delBranch){
                //del[i] = in;
                //i++;
                del.set(in);
            }
            v.setAddList(add);
            v.setDelList(del);
            listV.add(v);
        }
        return listV;
    }

    public BitSet getInitState() {
        return initState;
    }

    public void setActions(Hashtable<String, Action> list_actions) {
        for(String name : new ArrayList<String>(list_actions.keySet())){
            Action a = list_actions.get(name);
            insertAction(a, false);
        }
        indexAxioms = vaList.size();
    }

    private void setPrec2Act(VAction va, int[] prec){
        for(int index = 0 ;index<prec.length;index++){
            if(prec2Act.containsKey(prec[index])){
                Integer[] oldList = prec2Act.get(prec[index]);
                Integer[] newList = Arrays.copyOf(oldList, oldList.length + 1);
                newList[oldList.length] = vaList.indexOf(va);
                prec2Act.put(prec[index], newList);
            }else {
                Integer[] newList = new Integer[1];
                newList[0] = vaList.indexOf(va);
                prec2Act.put(prec[index], newList);
            }
        }
    }

    public VAction getAction(int index){
        return vaList.get(index);
    }

    public VAction getAction(String name){
        return vaList.get(actionsIndex.get(name));
    }

    public String printState(BitSet state){
        String ret = "";
        for (int i = state.nextSetBit(0); i >= 0; i = state.nextSetBit(i+1)) {
            ret = ret + " " + Predicates.get(i);
        }
        return ret;
    }

    public ArrayList<VAction> getVaList() {
        return vaList;
    }

    public void setAxioms(ArrayList<Action> axioms) {
        for(Action a : axioms){
            insertAction(a, true);
        }
    }

    public Integer insertAction(Action a, boolean isAxiom){
        VAction va = new VAction();
        va.setName(a.Name);
        va.cost = a.cost;
        int[] prec = new int[a._precond.size()];
        int i = 0;
        for(String s : a._precond){
            va.setBitPrecond(Predicates.inverse().get(s));
            prec[i] = Predicates.inverse().get(s);
            i++;
        }
        /*Reading non deterministic branches.
        * Limited to one nondeterministic effect per action!
        * NOTE: In fact one non-deterministic effect means maximum 2 branches per action
        * Plus the conditional effects
        * I.e. conditional effects + (one of) in the same action.
        * */
        // Non deterministic actions:
        for(Effect e : a._Effects){
            if(!a._Branches.isEmpty()){
                va.isNondeterministic = true;
                va.addEffects(createNondeterministicEffects(e,a));
            }else{
                va.addEffect(createEffects(e));
            }
        }
        //Observations: No effects and 2 branches:
        if(a._Effects.isEmpty() && !a._Branches.isEmpty()){
            va.isNondeterministic = true;
            va.addEffects(getBranches(a));
        }
        if(a.IsObservation) va.isObservation = true;
        if(isAxiom) vAxioms.add(va);
    	vaList.add(va);
        //Set prec2act:
        va.index = vaList.indexOf(va);
        if(a.Name.contains("Modify_human_")) humanActions.set(va.index);
        actionsIndex.put(va.getName(), va.index);
        setPrec2Act(va, prec);
        return va.index;
    }

    private ArrayList<VEffect> getBranches(Action a){
        ArrayList<VEffect> listV = new ArrayList<VEffect>();
        for(Branch b : a._Branches){
            VEffect v = new VEffect();
            ArrayList<Integer> addBranch = new ArrayList<Integer>();
            ArrayList<Integer> delBranch = new ArrayList<Integer>();
            for(String bnondet : b._Branches){
                if(bnondet.startsWith("~")){
                    delBranch.add(Predicates.inverse().get(bnondet.substring(1)));
                }else{
                    addBranch.add(Predicates.inverse().get(bnondet));
                }
            }
            //int[] add = new int[addBranch.size()];
            BitSet add = new BitSet();
            BitSet del = new BitSet();
            //int[] del = new int[delBranch.size()];
            //int i = 0;
            for(Integer in : addBranch){
                //add[i] = in;
                add.set(in);
                //i++;
            }
            //int i = 0;
            for(Integer in : delBranch){
                //del[i] = in;
                del.set(in);
                //i++;
            }
            v.setAddList(add);
            v.setDelList(del);
            listV.add(v);
        }
        return listV;
    }

    public void setDeterminizedObs(ArrayList<Action> obsHeuristics) {
        //Set the actions observation flag to true
        for(Action a : obsHeuristics){
            Integer index = insertAction(a, false);
            hObservations.add(getAction(index));
            getAction(index).isObservation = true;
        }
    }

    public int[] initLayers(BitSet state) {
        //1 Init list of scheduled actions: no action scheduled
        int[] factsLayer = new int[getSize()];
        Arrays.fill(factsLayer, Integer.MAX_VALUE);
        //2 For every predicate that is in the current state, update facts layer to put a 0 value
        for (int i = state.nextSetBit(0); i >= 0; i = state.nextSetBit(i+1)) {
            factsLayer[i] =0;
        }
        return factsLayer;
    }

    public int insertHumanObservation(VAction a, int cost) {
        VAction va = new VAction();
        va.setName(a.getName()+"HUMAN");
        va.cost = cost;

        va.isNondeterministic = true;
        va.isObservation = true;

        for(VEffect e : a.getEffects()){
            VEffect eff = new VEffect();
            eff.setAddList((BitSet) e.getAddList().clone());
            eff.setDelList((BitSet) e.getDelList().clone());
            va.addEffect(eff);
        }
        vaList.add(va);
        //Set prec2act:
        va.index = vaList.indexOf(va);
        actionsIndex.put(va.getName(), va.index);
        setVectorCosts();
        return va.index;
    }

    public void setVectorCosts(){
        cost = new int[vaList.size()];
        for(int i=0;i < vaList.size() ;i++){
            cost[i] = vaList.get(i).cost;
        }

    }

    public void determinizeBranches(Action a) {
        VAction va0 = new VAction();
        VAction va1 = new VAction();
        va0.setName(a.Name + "#1");
        va1.setName(a.Name + "#2");
        va0.cost = a.cost;
        va1.cost = a.cost;
        va0.isNondeterministic = a._IsNondeterministic;
        va1.isNondeterministic = a._IsNondeterministic;
        va0.isObservation = a.IsObservation;
        va1.isObservation = a.IsObservation;

        int[] prec = new int[a._precond.size()];
        int i = 0;
        for(String s : a._precond){
            va0.setBitPrecond(Predicates.inverse().get(s));
            va1.setBitPrecond(Predicates.inverse().get(s));
            prec[i] = Predicates.inverse().get(s);
            i++;
        }
        /*Reading non deterministic branches.
        * Limited to one nondeterministic effect per action!
        * NOTE: In fact one non-deterministic effect means maximum 2 branches per action
        * Plus the conditional effects
        * I.e. conditional effects + (one of) in the same action.
        * */
        // Non deterministic actions:
        //Branch 0
        VEffect eff0 = createEffectFromList(a._Branches.get(0)._Branches);
        va0.addEffect(eff0);
        VEffect eff1 = createEffectFromList(a._Branches.get(1)._Branches);
        va1.addEffect(eff1);

        vaList.add(va0);
        vaList.add(va1);

        //Set prec2act:
        va0.index = vaList.indexOf(va0);
        va1.index = vaList.indexOf(va1);
        actionsIndex.put(va0.getName(), va0.index);
        actionsIndex.put(va1.getName(), va1.index);
        setPrec2Act(va0, prec);
        setPrec2Act(va1, prec);
    }

    public void setActionsUsed(int action) {
        actionsUsed.set(action);
    }

    public void cleanActionsUsed() {
        actionsUsed.clear();
    }

    public BitSet humanUsed(){
        BitSet bS = (BitSet) actionsUsed.clone();
        bS.and(humanActions);
        //CAREFUL!
        return bS;
    }
}
