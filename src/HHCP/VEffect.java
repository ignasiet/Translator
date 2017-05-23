package HHCP;

/**
 * Created by ignasi on 15/05/17.
 */
public class VEffect {
    private int[] condition;
    private int[] addList;
    private int[] delList;

    public VEffect(){

    }

    public void setCondition(int[] cond){
        condition = cond;
    }

    public void setAddList(int[] addList) {
        this.addList = addList;
    }

    public void setDelList(int[] delList) {
        this.delList = delList;
    }

    public int[] getCondition() {
        return condition;
    }

    public int[] getAddList() {
        return addList;
    }

    public int[] getDelList() {
        return delList;
    }
}
