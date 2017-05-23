package HHCP;

import com.sun.org.apache.xml.internal.utils.Trie;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;

/**
 * Created by ignasi on 18/05/17.
 */
public class TrieNode {

    public BitSet partialState = new BitSet();
    public boolean isTerminal = false;
    private HashMap<Integer, TrieNode> children = new HashMap<Integer, TrieNode>();
    int action = -1;
    int cost = Integer.MAX_VALUE;
    boolean marked = true;

    public void put(BitSet r, int setIndex, int indexAction) {
        int i = r.nextSetBit(setIndex);
        if(i<0){
            //Nao possui mais 1, entao pára neste filho
            action = indexAction;
            isTerminal = true;
            return;
        }
        if(!children.containsKey(i)){
            TrieNode child = new TrieNode();
            partialState.set(i);
            child.partialState.set(i);
            children.put(i, child);
        }
        children.get(i).put(r, i+1, indexAction);
    }

    public TrieNode getChildrenAt(int index){
        return children.get(index);
    }
}
