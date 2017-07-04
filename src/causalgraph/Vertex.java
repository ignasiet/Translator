/**
 * 
 */
package causalgraph;

import org.jgrapht.ext.VertexNameProvider;

/**
 * @author ignasi
 *
 */
public class Vertex implements VertexNameProvider<String>{

	@Override
	public String getVertexName(String arg0) {
		return arg0.toString();
	}
	
}
