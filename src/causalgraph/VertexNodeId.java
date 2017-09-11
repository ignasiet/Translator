package causalgraph;

import org.jgrapht.ext.VertexNameProvider;

/**
 * Created by ignasi on 11/09/17.
 */
public class VertexNodeId implements VertexNameProvider<VertexNode> {

    @Override
    public String getVertexName(VertexNode vertexNode) {
        return String.valueOf(vertexNode.getId());
    }


}
