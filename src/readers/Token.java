/**
 * 
 */
package readers;

import java.io.StreamTokenizer;

/**
 * @author ignasi
 *
 */
public class Token {

	/**
	 * 
	 */
	public int type;
    public String text;
    public int line;
		
	public Token(StreamTokenizer tzr)
    {
        this.type = tzr.ttype;
        this.text = tzr.sval;
        this.line = tzr.lineno();
    }

}
