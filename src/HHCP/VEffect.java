package HHCP;

import java.util.BitSet;

/**
 * Created by ignasi on 15/05/17.
 */
public class VEffect {
    //private int[] condition;
    private BitSet condition;
    private BitSet addList;
    //private int[] addList;
    private BitSet delList;

    public VEffect(){
        condition = new BitSet();
    }

    public void setCondition(BitSet cond){
        condition = cond;
    }

    public void setAddList(BitSet addList) {
        this.addList = addList;
    }

    public void setDelList(BitSet delList) {
        this.delList = delList;
    }

    public BitSet getCondition() {
        return condition;
    }

    public BitSet getAddList() {
        return addList;
    }

    public BitSet getDelList() {
        return delList;
    }
}
