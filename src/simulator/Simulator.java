package simulator;

import HHCP.*;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Scanner;

/**
 * Created by ignasi on 30/05/17.
 */
public class Simulator {

    public Simulator(PartialPolicy policyP, BitSet initState, Problem problem, Problem heuristicProblem){
        if(policyP != null){
            simulatePolicy(policyP, initState, problem);
        }else{
            //simulateSearch(initState, problem, heuristicProblem, j, h);
        }
    }

    private void simulateSearch(BitSet initState, Problem problem, Problem hproblem, JustificationGraph jG, String heuristic) {
        Scanner reader = new Scanner(System.in);  // Reading from System.in
        Heuristic h = new Heuristic(hproblem, null, jG, heuristic);
        Node node = new Node(initState);
        node.setActionCounter(new int[problem.getVaList().size()]);
        //node.setActionLayer(new int[problem.getVaList().size()]);
        int[] factlayer = problem.initLayers(node.getState());
        node.setFacts(factlayer);
        while(!node.holds(problem.getGoal())){
            h.getValue(node);
            System.out.println("Heuristic action:");
            System.out.println(node.preferredAction);
            System.out.println("Applicable actions:");
            ArrayList<VAction> applicableActions = getApplicableActions(node, problem);
            for (VAction va : applicableActions) {
                System.out.println(applicableActions.indexOf(va) + ": "+ va.getName());
            }
            int chosenAct = reader.nextInt(); // Scans the next token of the input as an int.
            while(chosenAct<0 || chosenAct > applicableActions.size()){
                System.out.println("Wrong number!, enter again:");
                chosenAct = reader.nextInt();
            }
            if(applicableActions.get(chosenAct).isNondeterministic){
                System.out.println("Non-deterministic action " + applicableActions.get(chosenAct).getName() + ", choose effect: ");
                System.out.println("0-" + applicableActions.get(chosenAct).getName());
                System.out.println("1- not " + applicableActions.get(chosenAct).getName());
                System.out.println("Enter a number: ");
                int chosenEffect = reader.nextInt(); // Scans the next token of the input as an int.
                while(!(chosenEffect>=0 && chosenEffect<2)){
                    System.out.println("Wrong number!, enter again:");
                    chosenEffect = reader.nextInt();
                }
                /*int[] factlayer = problem.initLayers(node.getState());
                node.setActionCounter(new int[problem.getVaList().size()]);
                node.setActionLayer(new int[problem.getVaList().size()]);
                node.setFacts(factlayer);*/
                node= node.applyEffect(applicableActions.get(chosenAct).getEffects().get(chosenEffect), problem);
                //node.fixedPoint(problem);
            }else{
                /*int[] factlayer = problem.initLayers(node.getState());
                node.setActionCounter(new int[problem.getVaList().size()]);
                node.setActionLayer(new int[problem.getVaList().size()]);
                node.setFacts(factlayer);*/
                node = node.applyDeterministicAction(applicableActions.get(chosenAct), problem);
            }
        }
    }
    private ArrayList<VAction> getApplicableActions(Node node, Problem problem) {
        ArrayList<VAction> retList = new ArrayList<VAction>();
        for(VAction va : problem.getVaList()){
            if(va.getName().startsWith("K-axiom-")) continue;
            if(node.holds(va.getPreconditions())){
                retList.add(va);
            }
        }
        return retList;
    }

    public void simulatePolicy (PartialPolicy policyP, BitSet initState, Problem problem) {
        Node n = searchHelper.initLayers(new Node(initState), problem);
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
                System.out.println("0-" + action.getName());
                System.out.println("1- not " + action.getName());
                System.out.println("Enter a number: ");
                int chosenEffect = reader.nextInt(); // Scans the next token of the input as an int.
                while(!(chosenEffect>=0 && chosenEffect<2)){
                    System.out.println("Wrong number!, enter again:");
                    chosenEffect = reader.nextInt();
                }
                n= n.applyEffect(action.getEffects().get(chosenEffect), problem);
                n.fixedPoint(problem);
            } else {
                System.out.println("Deterministic action: " + action.getName());
                Node succ = n.applyDeterministicAction(action, problem);
                n = succ;
            }
            n = searchHelper.initLayers(new Node(n.getState()), problem);
        }
    }
}
