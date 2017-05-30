package simulator;

import HHCP.Node;
import HHCP.PartialPolicy;
import HHCP.Problem;
import HHCP.VAction;

import java.util.BitSet;
import java.util.Scanner;

/**
 * Created by ignasi on 30/05/17.
 */
public class Simulator {

    public Simulator (PartialPolicy policyP, BitSet initState, Problem problem) {
        Node n = new Node(initState);
        boolean solved = false;
        Scanner reader = new Scanner(System.in);  // Reading from System.in
        while(!solved) {
            if (n.holds(problem.getGoal())) {
                System.out.println("Goal Reached!");
                solved = true;
                return;
            }
            int act = policyP.action(n.getState());
            if (act == -1) {
                System.out.println("Error! State not handled");
                return;
            }
            VAction action = problem.getAction(act);
            if (action.isNondeterministic) {
                System.out.println("Non-deterministic action " + action.getName() + ", choose effect: ");
                System.out.println("0-" + problem.getPredicate(action.getEffects().get(0).getAddList()[0]));
                System.out.println("1-" + problem.getPredicate(action.getEffects().get(1).getAddList()[0]));
                System.out.println("Enter a number: ");
                int chosenEffect = reader.nextInt(); // Scans the next token of the input as an int.
                while(!(chosenEffect>=0 && chosenEffect<2)){
                    System.out.println("Wrong number!, enter again:");
                    chosenEffect = reader.nextInt();
                }
                n= n.applyEffect(action.getEffects().get(chosenEffect));

            } else {
                System.out.println("Deterministic action: " + action.getName());
                Node succ = n.applyDeterministicAction(action);
                n = succ;
            }
        }
    }
}
