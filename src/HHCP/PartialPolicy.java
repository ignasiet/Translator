package HHCP;

import java.util.*;

/**
 * Created by ignasi on 18/05/17.
 */
public class PartialPolicy {

    private TrieNode root = new TrieNode();
    public HashMap<BitSet, Boolean> marked = new HashMap<>();
    public HashMap<BitSet, Integer> partial = new HashMap<>();

    /**Returns action index or -1*/
    public int find(BitSet s){
        //TrieNode node = findNode(s);
        //if(node == null) return -1;
        //return node.action;
    	return action(s);
    }

    public boolean exists(BitSet s){
        TrieNode node = findNode(s);
        if(node == null){
            return false;
        }else{
            return node.marked;
        }
    }

    /**Returns node or null*/
    public TrieNode findNode(BitSet s){
        TrieNode node = root;
        int size = node.partialState.size();
        int i = 0;
        int j=0;
        while(i < size){
            i = node.partialState.nextSetBit(i);
            if(i < 0) {
                if (node.isTerminal) {
                    //There are no more 1s and the node is terminal
                    return node;
                } else {
                    //Node is not terminal and has no more 1s: not common
                    //node = root;
                    //i=j;
                    return null;
                }
            }
            if(s.get(i)) {
                //There is a one 1s in the position: continue searching in its successors.
                node = node.getChildrenAt(i);
                j=i;
                i++;
            }else{
                //There is not 1s in the first position of the node. Move right i and continue.
                i++;
            }
        }
        //Base case: the pointer reached the end of the bit set.
        return null;
    }

    /**Returns action index or -1*/
    public void mark(BitSet s, boolean value){
        TrieNode node = findNode(s);
        node.marked= value;
    }

    public void put(BitSet r, int indexAction) {
        if(marked.containsKey(r) || partial.containsKey(r)){
            if(partial.get(r) != indexAction) {
                System.out.println("Conflict! between action " + partial.get(r) + " and " + indexAction);
                return;
            }
    	}
        marked.put((BitSet) r.clone(), true);
        partial.put((BitSet) r.clone(), indexAction);
        root.put(r, 0, indexAction);
    }

    public void clear() {
        root = new TrieNode();
        partial.clear();
        marked.clear();
    }

    public int size(){
        int size = 0;
        for(BitSet bs : marked.keySet()){
            if(marked.get(bs)) size++;
        }
        return size;
    }

    public boolean valid(BitSet s){
        if(marked.containsKey(s)) return marked.get(s);
        for(BitSet li : marked.keySet()){
        	BitSet A = (BitSet) li.clone();
    		A.and(s);
    		if(A.equals(li)){
    			//Found the match!
    			return marked.get(li);
    		}
        }
        return false;
    }

    /**Returns the index of the action or -1 if there is no state that entails s*/
    public int action(BitSet s){
    	//BitSet[] li = (BitSet[]) marked.keySet().toArray();
        if(partial.containsKey(s)) return partial.get(s);
    	boolean found = false;
    	//int i = 0;
    	BitSet bestShot = new BitSet();
    	for(BitSet li : partial.keySet()){
    		BitSet A = (BitSet) li.clone();
    		A.and(s);
    		if(A.equals(li)){
    			//Found the match!
    			if(li.cardinality() > bestShot.cardinality()){
    				bestShot = (BitSet) li.clone();
    			}
    			found = true;
    			//i++;
    		}
    	}
    	if(found) return partial.get(bestShot);
    	return -1;
    }

    public Set<BitSet> iteratorStatesActions() {
        return marked.keySet();
    }
}
