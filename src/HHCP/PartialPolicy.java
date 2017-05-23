package HHCP;

import java.util.*;

/**
 * Created by ignasi on 18/05/17.
 */
public class PartialPolicy {

    private TrieNode root = new TrieNode();
    public HashMap<BitSet, Boolean> marked = new HashMap<>();

    /**Returns action index or -1*/
    public int find(BitSet s){
        TrieNode node = root;
        int size = node.partialState.size();
        int i = 0;
        while(i < size){
            i = node.partialState.nextSetBit(i);
            if(i < 0) {
                if (node.isTerminal) {
                    //There are no more 1s and the node is terminal
                    return node.action;
                } else {
                    //Node is not terminal and has no more 1s: not common
                    return -1;
                }
            }
            if(s.get(i)) {
                //There is a one 1s in the position: continue searching in its successors.
                node = node.getChildrenAt(i);
                i++;
            }else{
                //There is not 1s in the first position of the node. Move right i and continue.
                i++;
            }
        }
        //Base case: the pointer reached the end of the bit set.
        return -1;
    }

    public void put(BitSet r, int indexAction) {
        marked.put((BitSet) r.clone(), true);
        root.put(r, 0, indexAction);
    }

    public void clear() {
        root = new TrieNode();
        marked.clear();
    }

    public Set<BitSet> iteratorStatesActions() {
        return marked.keySet();
    }
}
