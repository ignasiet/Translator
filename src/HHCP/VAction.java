package HHCP;

import java.util.ArrayList;
import java.util.BitSet;

/**
 * Created by ignasi on 15/05/17.
 */
public class VAction {

    public BitSet preconditions;
    private String Name;
    public boolean isNondeterministic = false;
    public int cost = 1;
    public int index;

    private ArrayList<VEffect> effects = new ArrayList<VEffect>();

    public VAction(){
        preconditions = new BitSet();
    }

    public BitSet getPreconditions() {
        return preconditions;
    }

    public int[] getPreconditionArray(){
        int[] prec = new int[preconditions.cardinality()];
        int i = 0;
        for(int pr = preconditions.nextSetBit(0); pr >= 0; pr = preconditions.nextSetBit(pr+1)){
            prec[i] = pr;
            i++;
        }
        return prec;
    }

    public String getName() {
        return Name;
    }

    public void setName(String name) {
        Name = name;
    }

    /*public void addPreconditions(int[] prec) {
        preconditions = prec;
    }*/

    public void addEffect(VEffect eff){
        effects.add(eff);
    }

    public void addEffects(ArrayList<VEffect> veffs){
        effects.addAll(veffs);
    }

    public ArrayList<VEffect> getEffects() {
        return effects;
    }

    public void setBitPrecond(Integer index) {
        preconditions.set(index);
    }
}
