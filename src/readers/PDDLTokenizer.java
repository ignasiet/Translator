/**
 * 
 */
package readers;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.io.StreamTokenizer;
import java.io.StringReader;
import java.util.Iterator;

/**
 * @author ignasi
 *
 */
public class PDDLTokenizer implements Iterator<Token>{

	/**
	 * @throws IOException 
	 * 
	 */
	// Instance variables have default access to allow unit tests access.
	String strLine;
	StreamTokenizer tokenizedStream;
	IOException m_ioexn;
	
	public PDDLTokenizer(String src)
    {
        this(new StringReader(src));
    }	
	
	
	public PDDLTokenizer(Reader r){
		if(r == null)
            r = new StringReader("");
        BufferedReader buffrdr = new BufferedReader(r);
		tokenizedStream = new StreamTokenizer(buffrdr);
		tokenizedStream.resetSyntax(); // We don't like the default settings		 
		tokenizedStream.whitespaceChars(0, ' ');
		tokenizedStream.wordChars(' '+1,255);
		tokenizedStream.ordinaryChar('(');
		tokenizedStream.ordinaryChar(')');
		tokenizedStream.ordinaryChar('\'');
        tokenizedStream.commentChar(';');
        tokenizedStream.quoteChar('"');
	}
	
	/** Return the most recently caught IOException, if any,
     * 
     * @return
     */
    public IOException getIOException()
    {
        return m_ioexn;
    }
	
	public Token next()
    {
        try
        {
        	tokenizedStream.nextToken();
        }
        catch(IOException e)
        {
            m_ioexn = e;
            return null;
        }
 
        Token token = new Token(tokenizedStream);
        return token;
    }
	
	public Token peekToken()
    {	
        if(m_ioexn != null)
            return null;
        try
        {
        	tokenizedStream.nextToken();
        }
        catch(IOException e)
        {
            m_ioexn = e;
            return null;
        }
        if(tokenizedStream.ttype == StreamTokenizer.TT_EOF)
            return null;
        Token token = new Token(tokenizedStream);
        tokenizedStream.pushBack();
        return token;
    }
	
	public boolean hasNext()
    {
        if(m_ioexn != null)
            return false;
        try
        {
        	tokenizedStream.nextToken();
        }
        catch(IOException e)
        {
            m_ioexn = e;
            return false;
        }
        if(tokenizedStream.ttype == StreamTokenizer.TT_EOF)
            return false;
        tokenizedStream.pushBack();
        return true;
    }

	@Override
	public void remove() {
		// TODO Auto-generated method stub
		
	}

}
