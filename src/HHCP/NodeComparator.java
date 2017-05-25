package HHCP;

import java.util.Comparator;


/**
 * Created by ignasi on 16/05/17.
 */
public class NodeComparator implements Comparator<Node>{

    @Override
    public int compare(Node x, Node y)
    {
        // Assume neither string is null. Real code should
        // probably be more robust
        // You could also just return x.length() - y.length(),
        // which would be more efficient.
        if (x.getFunction() < y.getFunction())
        {
            return -1;
        }
        if (x.getFunction() > y.getFunction())
        {
            return 1;
        }
        return 0;
    }

}
