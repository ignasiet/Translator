package HHCP;

import java.util.Comparator;


/**
 * Created by ignasi on 16/05/17.
 */
public class fNodeComparator implements Comparator<fNode>{

    @Override
    public int compare(fNode x, fNode y){
    	return Float.compare(x.getH(), y.getH());
    }

}
