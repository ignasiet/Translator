package landmark;

import java.util.ArrayList;
import java.util.Hashtable;

/* @author ignasi
        *
        */
public class NodeLandmark {

    /**
     *
     */
    private ArrayList<NodeLandmark> predecessors = new ArrayList<NodeLandmark>();
    private Hashtable<String, Integer> predecessors_hash = new Hashtable<String, Integer>();
    private ArrayList<NodeLandmark> successors = new ArrayList<NodeLandmark>();
    public int level;
    public String predicate;
    public boolean solved = false;

    public NodeLandmark(String pred) {
        //Constructor
        predicate = pred;
        level = 1000000000;
    }

    public String toString(){
        return predicate;
    }

    public void addSuccessor(NodeLandmark successor){
        successors.add(successor);
    }

    public void addPredecessor(NodeLandmark predecessor){
        if(!predecessors_hash.containsKey(predecessor.predicate)){
            predecessors.add(predecessor);
            predecessors_hash.put(predecessor.predicate, 1);
        }
    }

    public ArrayList<NodeLandmark> getParent(){
        return predecessors;
    }

    public boolean hasParent(){
        if(!predecessors.isEmpty()){
            return true;
        }
        else{
            return false;
        }
    }

    public int hashCode(){
        return predicate.hashCode();
    }
}
