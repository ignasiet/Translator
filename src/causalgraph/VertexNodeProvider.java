package causalgraph;
import org.jgrapht.ext.VertexNameProvider;

/**
 * @author ignasi
 *
 */
public class VertexNodeProvider implements VertexNameProvider<VertexNode> {

    @Override
    public String getVertexName(VertexNode vertexNode) {
        return vertexNode.getLabel();
    }
}

