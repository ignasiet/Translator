/**
 * 
 */
package causalgraph;

import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DefaultWeightedEdge;

/**
 * @author ignasi
 *
 */
public class Edge<V> extends DefaultWeightedEdge {
    private V v1;
    private V v2;
    private String label;

    public Edge(V v1, V v2, String label) {
        this.v1 = v1;
        this.v2 = v2;
        this.label = label;
    }

    public V getV1() {
        return v1;
    }

    public V getV2() {
        return v2;
    }

    public String toString() {
        return label;
    }

    public String getSource(){
        return v1.toString();
    }

    public String getTarget(){
        return v2.toString();
    }

}