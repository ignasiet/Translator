package causalgraph;

/**
 * Created by ignasi on 11/09/17.
 */
public class VertexNode {

    private String label;
    private int id;

    public VertexNode(String field, int i) {
        label = field;
        id = i;
    }

    public String getLabel(){
        return label;
    }

    public int getId(){
        return id;
    }

    @Override
    public boolean equals(Object obj) {

        if (obj.getClass().getPackage()
                .equals(this.getClass().getPackage())
                && obj.getClass().getName()
                .equals(this.getClass().getName())) {

            VertexNode vertex = (VertexNode) obj;

            if (id == vertex.getId())
                return true;
        }

        // Else
        return false;
    }

    @Override
    public int hashCode() {
        // No need for a perfect hash
        return id;
    }
}
