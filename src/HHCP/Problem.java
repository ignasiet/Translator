package HHCP;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import pddlElements.Action;
import pddlElements.Axiom;
import pddlElements.Branch;
import pddlElements.Effect;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Hashtable;

/**
 * Created by ignasi on 15/05/17.
 */
public class Problem {

    private BiMap<Integer, String> Predicates;

    private BitSet initState;
    private BitSet goalSet;
    private int[] goal;
    public Hashtable<Integer, Integer[]> prec2Act = new Hashtable<Integer, Integer[]>();
    private ArrayList<VAction> vaList = new ArrayList<VAction>();
    private int size;

    public Problem(ArrayList<String> predicates) {
        Predicates = HashBiMap.create();
        size = predicates.size();
        //initState = new BitSet(size);
        initState = new BitSet();
        goalSet = new BitSet();
        int i = 0;
        for(String predicate : predicates){
            Predicates.put(i, predicate);
            i++;
        }
    }

    public BitSet getGoalSet(){
        return goalSet;
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
        goal = new int[goalState.size()];
        int i = 0;
        for(String s : goalState){
            goal[i] = Predicates.inverse().get(s);
            goalSet.set(Predicates.inverse().get(s));
            i++;
        }
    }

    public String getPredicate(int index){
        return Predicates.get(index);
    }

    public int[] getGoal() {
        return goal;
    }

    public VEffect createEffects(Effect e){
        VEffect v = new VEffect();
        int[] cond = new int[e._Condition.size()];
        int i = 0;
        for(String condition : e._Condition){
            cond[i] = Predicates.inverse().get(condition);
            i++;
        }
        v.setCondition(cond);
        ArrayList<Integer> addList = new ArrayList<Integer>();
        ArrayList<Integer> delList = new ArrayList<Integer>();
        for(String effect : e._Effects){
            if(effect.startsWith("~")){
                delList.add(Predicates.inverse().get(effect.substring(1)));
            }else{
                addList.add(Predicates.inverse().get(effect));
            }
        }
        int[] add = new int[addList.size()];
        int[] del = new int[delList.size()];
        i = 0;
        for(Integer in : addList){
            add[i] = in;
            i++;
        }
        i = 0;
        for(Integer in : delList){
            del[i] = in;
            i++;
        }
        v.setAddList(add);
        v.setDelList(del);
        return v;
    }

    public ArrayList<VEffect> createNondeterministicEffects(Effect e, Action a){
        ArrayList<VEffect> listV = new ArrayList<VEffect>();
        int[] cond = new int[e._Condition.size()];
        int i = 0;
        for(String condition : e._Condition){
            cond[i] = Predicates.inverse().get(condition);
            i++;
        }
        //Effects
        ArrayList<Integer> addList = new ArrayList<Integer>();
        ArrayList<Integer> delList = new ArrayList<Integer>();
        for(String effect : e._Effects){
            if(effect.startsWith("~")){
                delList.add(Predicates.inverse().get(effect.substring(1)));
            }else{
                addList.add(Predicates.inverse().get(effect));
            }
        }
        for(Branch b : a._Branches){
            VEffect v = new VEffect();
            v.setCondition(cond);
            ArrayList<Integer> addBranch = new ArrayList<Integer>();
            ArrayList<Integer> delBranch = new ArrayList<Integer>();
            for(String bnondet : b._Branches){
                if(bnondet.startsWith("~")){
                    delBranch.add(Predicates.inverse().get(bnondet.substring(1)));
                }else{
                    addBranch.add(Predicates.inverse().get(bnondet));
                }
            }
            addBranch.addAll(addList);
            delBranch.addAll(delList);
            int[] add = new int[addBranch.size()];
            int[] del = new int[delBranch.size()];
            i = 0;
            for(Integer in : addBranch){
                add[i] = in;
                i++;
            }
            i = 0;
            for(Integer in : delBranch){
                del[i] = in;
                i++;
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
            insertAction(a);
        }
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
            insertAction(a);
        }
    }

    private void insertAction(Action a){
        VAction va = new VAction();
        va.setName(a.Name);
        int[] prec = new int[a._precond.size()];
        int i = 0;
        for(String s : a._precond){
            va.setBitPrecond(Predicates.inverse().get(s));
            prec[i] = Predicates.inverse().get(s);
            i++;
        }
        //va.addPreconditions(prec);
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
        vaList.add(va);
        //Set prec2act:
        va.index = vaList.indexOf(va);
        setPrec2Act(va, prec);
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
            int[] add = new int[addBranch.size()];
            int[] del = new int[delBranch.size()];
            int i = 0;
            for(Integer in : addBranch){
                add[i] = in;
                i++;
            }
            i = 0;
            for(Integer in : delBranch){
                del[i] = in;
                i++;
            }
            v.setAddList(add);
            v.setDelList(del);
            listV.add(v);
        }
        return listV;
    }
}
