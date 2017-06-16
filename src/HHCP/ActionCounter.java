package HHCP;

/**
 * Created by ignasi on 12/06/17.
 */
public class ActionCounter {
    //Counter for preconditions
    public int index;
    public int counter = Integer.MAX_VALUE;
    //Counter for effects
    public int[] eCounter;

    public ActionCounter(VAction va){
        index = va.index;
        eCounter = new int[va.getEffects().size()];
    }
}
