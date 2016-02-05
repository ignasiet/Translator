/**
 * 
 */
package readers;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.StreamTokenizer;

//import pddlObjects.Domain;

/**
 * @author ignasi
 *
 */
public class DomainReader {

	/**
	 * @throws IOException 
	 * 
	 */
	String strLine;
	StreamTokenizer tokenizedStream;
	IOException m_ioexn;
	
	public DomainReader(FileReader domainInput) throws IOException {
		// TODO Auto-generated constructor stub
		prepareTokenizer(domainInput);		
		//Domain domain = new Domain();
		int cursor = 0;
		if((cursor = strLine.indexOf("define"))!=0){
				
			}
			else if ((cursor = strLine.indexOf("requirements"))!=0){
				extractRequirements(cursor);
			}
			else if ((cursor = strLine.indexOf("types"))!=0){
				extractTypes(cursor);
			}
			else if ((cursor = strLine.indexOf("predicates"))!=0){
				extractPredicates(cursor);
			}
			else if ((cursor = strLine.indexOf("actions"))!=0){
				extractActions(cursor);
			}
			else if ((cursor = strLine.indexOf("objects"))!=0){
				extractObjects(cursor);
			}
		
	}
	
	private void prepareTokenizer(FileReader domainInput){
		BufferedReader bufRead = new BufferedReader(domainInput);
		tokenizedStream = new StreamTokenizer(bufRead);
		tokenizedStream.resetSyntax(); // We don't like the default settings		 
		tokenizedStream.whitespaceChars(0, ' ');
		tokenizedStream.wordChars(' '+1,255);
		tokenizedStream.ordinaryChar('(');
		tokenizedStream.ordinaryChar(')');
		tokenizedStream.ordinaryChar('\'');
        tokenizedStream.commentChar(';');
        tokenizedStream.quoteChar('"');
        try {
			bufRead.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
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

	private void extractObjects(int cursor) {
		// TODO Auto-generated method stub
		
	}
	private void extractActions(int cursor) {
		// TODO Auto-generated method stub
		
	}
	private void extractPredicates(int cursor) {
		// TODO Auto-generated method stub
		
	}
	private void extractTypes(int cursor) {
		// TODO Auto-generated method stub
		
	}
	private void extractRequirements(int cursor) {
		// TODO Auto-generated method stub
		
	}

}
