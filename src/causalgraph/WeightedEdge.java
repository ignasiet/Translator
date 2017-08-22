package causalgraph;

import org.jgrapht.graph.DefaultWeightedEdge;

/**
 * Created by ignasi on 21/08/17.
 */
public class WeightedEdge<V> extends DefaultWeightedEdge {
    private V v1;
    private V v2;
    private String label;

    public WeightedEdge(V v1, V v2, String label) {
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
}
