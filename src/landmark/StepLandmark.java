package landmark;
import java.util.ArrayList;
import java.util.Hashtable;

/**
 * @author ignasi
 *
 */
public class StepLandmark {

    /**
     *
     */
    private ArrayList<NodeLandmark> listNodes = new ArrayList<NodeLandmark>();
    private Hashtable<String, NodeLandmark> nodesHash = new Hashtable<String, NodeLandmark>();
    protected Hashtable<String, Integer> actionsHash = new Hashtable<String, Integer>();
    public StepLandmark father;
    public StepLandmark son;
    public int step;
    public ArrayList<String> levelGoals = new ArrayList<String>();

    public StepLandmark() {
    }

    public ArrayList<NodeLandmark> getIterator(){
        return listNodes;
    }

    public void addNode(NodeLandmark n){
        listNodes.add(n);
        nodesHash.put(n.predicate, n);
    }

    public NodeLandmark getNode(String p){
        return nodesHash.get(p);
    }

    public boolean Contains(String p){
        return nodesHash.containsKey(p);
    }

    public void updateParentNode(String node, NodeLandmark parent){
        NodeLandmark n = nodesHash.get(node);
        n.addPredecessor(parent);
    }

    public void updateSuccessorNode(String node, NodeLandmark successor){
        NodeLandmark n = nodesHash.get(node);
        n.addSuccessor(successor);
    }
}
