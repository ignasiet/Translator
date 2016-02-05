/**
 * 
 */
package readers;

//import pddlObjects.Domain;

/**
 * @author ignasi
 *
 */
public class PDDLParser {

	/**
	 * 
	 */
	PDDLTokenizer tokenizer;
	 
    public PDDLParser(PDDLTokenizer input)
    {
        tokenizer=input;
    }
 
    public class ParseException extends Exception{}
 
    public interface Expr
    {
        // abstract parent for Atom and ExprList
    }
 
    public Expr parseExpr() throws ParseException
    {
        Token token = tokenizer.next();
        switch(token.type)
        {
            case '(': return parseExprList(token);
            case '"': return new StringAtom(token.text);
            default: return new Atom(token.text);
        }
    }
 
 
    protected ExprList parseExprList(Token openParen) throws ParseException
    {
        ExprList acc = new ExprList();
        while(tokenizer.peekToken().type != ')')
        {
        	//Expr element should be mapped in the category that correspond (Action, Paramenter, etc...)
        	Expr element = parseExpr();
        	acc.add(element);         
        }
        Token closeParen = tokenizer.next();
        return acc;
    }   
 

}
