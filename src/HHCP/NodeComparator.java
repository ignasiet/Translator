package HHCP;

import java.util.Comparator;


/**
 * Created by ignasi on 16/05/17.
 */
public class NodeComparator implements Comparator<Node>{

    @Override
    public int compare(Node x, Node y){
        /*if (x.getFunction() < y.getFunction())
        {
            return -1;
        }
        if (x.getFunction() > y.getFunction())
        {
            return 1;
        }
        return 0;*/
    	//return Integer.compare(x.getFunction(), y.getFunction());
    	return Long.compare(x.getH(), y.getH());
    }

}
