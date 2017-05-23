package HHCP;

import java.util.ArrayList;

/**
 * Created by ignasi on 15/05/17.
 */
public class VAction {

    private int[] preconditions;
    private String Name;
    public boolean isNondeterministic = false;
    public int cost = 1;
    public int index;

    private ArrayList<VEffect> effects = new ArrayList<VEffect>();

    public VAction(){
    }

    public int[] getPreconditions() {
        return preconditions;
    }

    public String getName() {
        return Name;
    }

    public void setName(String name) {
        Name = name;
    }

    public void addPreconditions(int[] prec) {
        preconditions = prec;
    }

    public void addEffect(VEffect eff){
        effects.add(eff);
    }

    public void addEffects(ArrayList<VEffect> veffs){
        effects.addAll(veffs);
    }

    public ArrayList<VEffect> getEffects() {
        return effects;
    }
}
