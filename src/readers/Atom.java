/**
 * 
 */
package readers;

import readers.PDDLParser.Expr;

public class Atom implements Expr
{
    String name;
    public String toString()
    {
        return name;
    }
    public Atom(String text)
    {
        name = text;
    }
     
}