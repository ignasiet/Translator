package pddlElements;
import java.util.ArrayList;

import parser.ParserHelper;

/**
 * @author ignasi
 *
 */
public class Branch {
	public ArrayList<String> _Branches = new ArrayList<String>();
	
	public Branch(){}
	
	public String toString(String negateString){
		if(!_Branches.isEmpty()){
			String return_string = "(and ";
			for(String branch : _Branches){
				return_string = return_string + ParserHelper.negateString(branch, negateString);
			}
			return return_string + ")";
		}else{
			return null;
		}		
	}
	
}