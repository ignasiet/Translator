package HHCP;

import java.util.*;

/**
 * Created by ignasi on 15/05/17.
 */
public class Searcher {

    private Problem problem;
    private Problem HProblem;
    private HashSet<BitSet> visited = new HashSet<BitSet>();
    private HashSet<BitSet> seen = new HashSet<BitSet>();
    private Stack<BitSet> open = new Stack<BitSet>();
    private HashSet<BitSet> DeadEnds = new HashSet<BitSet>();
    private HashMap<BitSet, Integer> forbiddenStateActions = new HashMap<BitSet, Integer>();
    private BitSet forbiddenHelp = new BitSet();
    private BitSet forbiddenActions = new BitSet();
    private HashMap<BitSet, Integer> expectedCost = new HashMap<BitSet, Integer>();
    private HashMap<BitSet, BitSet> parent = new HashMap<BitSet, BitSet>();
    private PriorityQueue<Node> fringe;
    private Heuristic h;
    private PartialPolicy policyP = new PartialPolicy();
    private ArrayList<Integer> landmarks;
    private int upperBound = Integer.MAX_VALUE;


    public Searcher(Problem p, Problem heuristicP, ArrayList<String> l, JustificationGraph jG, String heuristic){
        problem = p;
        HProblem = heuristicP;
        int solCost = Integer.MAX_VALUE;
        boolean deadEndsFound = false;
        if(!l.isEmpty()){
            landmarks = new ArrayList<>();
            for(String landmark : l){
                if(!p.getInitState().get(p.getPredicate(landmark))){
                    landmarks.add(p.getPredicate(landmark));
                }
            }
        }
        h = new Heuristic(heuristicP, landmarks, jG, heuristic);
        h.useCosts(heuristicP.cost);
        //Search starts!
        double startTime = System.currentTimeMillis();
        boolean modified = true;
        while(modified){
            modified = false;
            open.add(p.getInitState());
            //Init the fact layer for the first time...
            HashMap<BitSet, Integer> parentAction = new HashMap<>();
            while(!open.isEmpty()){
                BitSet s = open.pop();
                if(!searchHelper.entails(s, problem.getGoal()) && !seen.contains(s)){
                    seen.add(s);
                    if(policyP.find(s)<0){
                        //System.out.println("State with no solution found.");
                        if(GenPlanPairs(s)){
                            modified = true;
                            //Mark State-Action Pairs
                            updateCost(s);
                            //System.out.println("Partial expected cost of the solution: " + expectedCost.get(p.getInitState()));
                            markStateActions();
                        }else {
                            System.out.println("Adding to Dead End Set the state: " + s.toString());
                            if(parentAction.containsKey(s)) forbiddenStateActions.put(regressStateAction(s, parentAction.get(s)), parentAction.get(s));
                            deadEndsFound=true;
                            break;
                        }
                    }
                    int indexAction = policyP.find(s);
                    //New verification: verify that the new pair is not marked yet!
                    if(!policyP.valid(s)){
                        applyAction(indexAction, s, parentAction);
                        modified = false;
                    }
                }
            }
            if(deadEndsFound){
                modified = true;
                processDeadEnds();
                deadEndsFound = false;
                clear();
                policyP.clear();
                //return;
            }
            //TODO: What to do with weak problems?
            //Here the solution must be compared to test:
            // * if there are other solutions without the human help actions used and best cost.
            System.out.println("Expected cost of the solution: " + expectedCost.get(p.getInitState()));
            /*BitSet bS = problem.humanUsed();
            if(!bS.isEmpty()){
                if(!previousSolution()){
                    for(int i=bS.nextSetBit(0);i>=0;i=bS.nextSetBit(i+1)){
                        forbiddenHelp.set(i);
                        modified = true;
                        System.out.println("Replanning: ");
                        clear();
                        problem.cleanActionsUsed();
                        policyP.clear();
                    }
                }
            }*/
        }
        //GenPlanPairs(problem.getInitState());
        double endTime = System.currentTimeMillis();
        searchHelper.printStats(policyP, startTime, endTime, p);
        searchHelper.printPolicy(p.getInitState(), policyP, p);
        //Simulator sim = new Simulator(policyP, p.getInitState(), problem, heuristicP);
    }

    private boolean previousSolution() {
        boolean ret = true;
        if(!policyP.containsOldPolicy()){
            ret = false;
            policyP.copyPolicyOld();
        }
        return ret;
    }

    private void clear(){
        visited.clear();
        seen.clear();
    }

    private BitSet regressStateAction(BitSet s, Integer action) {
        BitSet ancestor = (BitSet) s.clone();
        VAction a = problem.getAction(action);
        for (int p = a.preconditions.nextSetBit(0); p >= 0; p = a.preconditions.nextSetBit(p+1)) {
            //for(int p : a.getPreconditions()){
            ancestor.set(p);
        }
        boolean appliedEffect = true;
        for(VEffect e : a.getEffects()){
            //CAUTION HERE! verify the conditional effect has been applied before regressing it!
            BitSet A = (BitSet) e.getAddList().clone();
            A.and(ancestor);
            if(A.equals(e.getAddList())){
                for(int i = e.getAddList().nextSetBit(0); i>=0; i= e.getAddList().nextSetBit(i+1)){
                    ancestor.set(i,false);
                }
                ancestor.or(e.getCondition());
            }
        }
        return ancestor;
    }

    private void markStateActions() {
        for(BitSet bs : policyP.marked.keySet()){
            policyP.marked.put(bs, true);
        }
        boolean changed = true;
        while(changed){
            changed = false;
            for(BitSet bs : policyP.iteratorStatesActions()){
                if(searchHelper.entails(bs, problem.getGoal()) || !policyP.marked.get(bs)) continue;
                int indexAction = policyP.find(bs);
                VAction a = problem.getAction(indexAction);
                //Verify for each effect 2 conditions:
                ArrayList<BitSet> successors = new ArrayList<BitSet>();
                if(a.isNondeterministic) {
                    for (VEffect e : a.getEffects()) {
                        BitSet s = (BitSet) bs.clone();
                        //applyEffect(s, e);
                        BitSet resultEffect = applyEffect(s, e);
                        successors.add(resultEffect);
                    }
                }else{
                    BitSet s = (BitSet) bs.clone();
                    for(VEffect e : a.getEffects()) {
                        //applyEffect(s, e);
                        s.or(e.getAddList());
                        for(int i = e.getDelList().nextSetBit(0);i>=0;i=e.getDelList().nextSetBit(i+1)){
                            s.set(i, false);
                        }
                    }
                    successors.add(s);
                }
                /*With the new states verify the 2 conditions:
                    1 At least one successor is in the policy:
                    2 States returned are marked.
                If not children or goal nodes: remain marked true
                */
                for(BitSet successor : successors){
                    if(searchHelper.entails(successor, problem.getGoal())) continue;
                    //if(!policyP.marked.containsKey(successor) || !policyP.marked.get(successor)){
                    if(!policyP.valid(successor)){
                        policyP.marked.put(bs, false);
                        //policyP.partial.remove(bs);
                        changed = true;
                    }
                }
            }
        }
    }

    private void updateCost(BitSet s) {
        BitSet current = (BitSet) s.clone();
        while(parent.containsKey(current)){
            BitSet par = parent.get(current);
            int cost1 = expectedCost.get(par);
            int cost2 = expectedCost.get(current);
            int cost3 = problem.cost[policyP.action(par)];
            if(problem.getAction(policyP.action(par)).isNondeterministic){
                //MAX criterion
                //expectedCost.put(par, Math.max(cost1, cost2 + cost3));
                //ADD criterion?
                expectedCost.put(par, cost1 + cost2);
                current = (BitSet) par.clone();
            }else{
                //MAX criterion for deterministic actions
                expectedCost.put(par, Math.max(cost1, cost2 + cost3));
                //ADD criterion?
                //expectedCost.put(par, cost1 + cost2);
                current = (BitSet) par.clone();
            }

        }

    }

    private BitSet applyEffect(BitSet s, VEffect e){
        //TODO: Apply effects and non-deterministic points here!!!!
        /*s.or(e.getAddList());
        for(int i = e.getDelList().nextSetBit(0);i>=0;i=e.getDelList().nextSetBit(i+1)){
            s.set(i, false);
        }*/
        Node initNode = new Node(s);
        //TODO: how to recover the counters of action preconditions
        int[] factlayer = problem.initLayers(s);
        initNode.setFacts(factlayer);
        initNode.setActionCounterInc(problem);
        //initNode.setActionCounter(new int[problem.getVaList().size()]);
        initNode.setActionLayer(new int[problem.getVaList().size()]);
        Node returnNode = initNode.applyEffect(e, problem);
        return returnNode.getState();
    }

    private void applyAction(int indexAction, BitSet s, HashMap<BitSet, Integer> parentAction){
        VAction a = problem.getAction(indexAction);
        int costChild = 0;
        BitSet sCopy = (BitSet) s.clone();
        if(a.isNondeterministic){
            for(VEffect e : a.getEffects()){
                BitSet s2 = applyEffect((BitSet) s.clone(), e);
                parentAction.put(s2, indexAction);
                Node n = new Node(s2);
                //n.fixedPoint(n, problem.vAxioms);
                parent.put((BitSet) n.getState().clone(), (BitSet) s.clone());
                open.push((BitSet) n.getState().clone());
                if(expectedCost.containsKey(s2) && expectedCost.get(s2) > costChild){
                    costChild = expectedCost.get(s2);
                }
            }
            expectedCost.put(sCopy, costChild + problem.cost[indexAction]);
        }else{
            for(VEffect e : a.getEffects()){
                //applyEffect(s2, e);
                sCopy.or(e.getAddList());
                for(int i = e.getDelList().nextSetBit(0);i>=0;i=e.getDelList().nextSetBit(i+1)){
                    sCopy.set(i, false);
                }
            }
            BitSet s2 = (BitSet) sCopy.clone();
            parentAction.put(s2, indexAction);
            open.push(s2);
        }
    }

    private void printState(BitSet initState) {
        System.out.println("Printing state:");
        for(int i = initState.nextSetBit(0);i>=0;i=initState.nextSetBit(i+1)){
            System.out.println(i + ": " + problem.getPredicate(i));
        }
    }

    private void processDeadEnds() {
        //Get generalized dead-end
        for(BitSet s : DeadEnds) {
            if (parent.containsKey(s)) {
                forbiddenStateActions.put(parent.get(s), policyP.action(parent.get(s)));
                forbiddenActions.set(policyP.action(parent.get(s)));
            }
        }
        policyP.clear();
    }


    public boolean GenPlanPairs(BitSet initState){
        boolean solution = false;
        int solCost = 0;
        Comparator<Node> comparator = new NodeComparator();
        fringe = new PriorityQueue<Node>(100, comparator);
        Node initNode = new Node(initState);
        int[] factlayer = problem.initLayers(initState);
        initNode.setActionCounterInc(problem);
        initNode.setActionLayer(new int[problem.getVaList().size()]);
        initNode.setFacts(factlayer);
        //
        h.getValue(initNode);
        fringe.add(initNode);
        visited.clear();
        while(!solution) {
            if(fringe.isEmpty()){
                System.out.println("No weak plan found.\nThe initial State for this search may have caused a Dead-end.");
                //printState(initState);
                DeadEnds.add(initState);
                return false;
            }
            Node node = fringe.poll();
            if(visited(node)) continue;
            visited.add(node.getState());
            if(node.holds(problem.getGoal()) || policyP.valid(node.getState()) ){
                //solution = true;
                System.out.println("Solution found");
                //RegressPlan(node);
                RegressPlan(node);
                break;
            }
            /*EHC: take the first action of the policy. Usually does not work.
            * A* complete heuristic search.*/
            for (VAction va : getApplicableActions(node)) {
                if (forbiddenStateActions.containsKey(node.getState()) && forbiddenStateActions.get(node.getState()) == va.index)
                    continue;
                addToFringe(va, node);
            }

            /*EHC:
            if(!node.relaxedSolution.isEmpty()){
                VAction va = problem.getAction(node.preferredAction);
                addToFringe(va, node);
            }else {
                for (VAction va : getApplicableActions(node)) {
                    if (forbiddenStateActions.containsKey(node.getState()) && forbiddenStateActions.get(node.getState()) == va.index)
                        continue;
                    addToFringe(va, node);
                }
            }*/
        }
        //Review termination conditions
        return true;
    }

    private void addToFringe(VAction va, Node node){
        if (va.isNondeterministic) {
            ArrayList<Node> getSuccessorNodes = node.applyNonDeterministicAction(va, problem);
            int MaxH = 0;
            for (Node n : getSuccessorNodes) {
                //Review condition of adding the new state:
                if (!DeadEnds.contains(n.getState())) {
                    searchHelper.updateHeuristic(n, node, va, h);
                    if(n.getH() > MaxH){
                        MaxH = Math.toIntExact(n.getH());
                    }
                } else {
                    //Add this transition to the forbidden action state pair
                    MaxH = Integer.MAX_VALUE;
                    forbiddenStateActions.put(node.getState(), va.index);
                }
            }
            //Adicionar valor heuristico para as duas acoes
            String o1 = va.getName() + "#1";
            String o2 = va.getName() + "#2";
            h.updateValue(HProblem.getAction(o1).index,MaxH);
            h.updateValue(HProblem.getAction(o2).index,MaxH);
            for(Node n : getSuccessorNodes){
                n.setHeuristic(MaxH);
                n.setCost(MaxH);
                fringe.add(n);
            }
        } else {
            Node n = node.applyDeterministicAction(va, problem);
            if (!DeadEnds.contains(n.getState())) {
                /*if(visited.contains(n.getState())){
                    va = HProblem.getAction(node.relaxedSolution.get(node.relaxedSolution.size()-2));
                    va = problem.getAction(va.getName());
                    if(!va.isNondeterministic) n = node.applyDeterministicAction(va);
                }*/
                searchHelper.updateHeuristic(n, node, va, h);
                fringe.add(n);
            } else {
                //Add this transition to the forbidden action state pair
                forbiddenStateActions.put(node.getState(), va.index);
            }
        }
    }

	private boolean isSolvedNode(Node node) {
		return policyP.valid(node.getState());
	}

	/*private void updateHeuristic(Node child, Node father, VAction va) {
        child.setCost(father.getCost() + va.cost);
        child.setHeuristic(h.getValue(child));
    }*/

    private void RegressPlan(Node node){
    	BitSet r = (BitSet) node.getState().clone();
        expectedCost.put(node.getState(),0);
        int PlanCost = 0;
        while(node.parent != null){
            parent.put(node.getState(), node.parent.getState());
            VAction a = problem.getAction(node.indexAction);
            if(node.axioms != null) regressAxioms(node, r);
            //1 regress preconditions: put them all 1
            r.or(a.preconditions);
            //Regress effects
            regressNode(a,node,r);
            policyP.put((BitSet) r.clone(), node.indexAction);
            PlanCost+=problem.cost[node.indexAction];
            problem.setActionsUsed(node.indexAction);
            //System.out.println(problem.getAction(node.indexAction).getName());
            expectedCost.put(node.parent.getState(), PlanCost);
            node = node.parent;
        }
        //PlanCost+=problem.cost[node.indexAction];
        expectedCost.put(node.getState(), PlanCost);
        return;
    }

    private void regressAxioms(Node node, BitSet r) {
    	for (int i=node.axioms.size()-1; i>=0;i--) {
    		int index = node.axioms.get(i);
    		VAction ax = problem.getAction(index);
            r.or(ax.preconditions);
        	for(VEffect e : ax.getEffects()){
                for(int j = e.getAddList().nextSetBit(0); j>=0;j=e.getAddList().nextSetBit(j+1)){
                    //TODO: vvvv verify regression here! vvvvv
                    if(!node.parent.getState().get(j)){
                        r.set(j,false);
                    }
                }
            }
    	}
	}

	private void regressNode(VAction a, Node node, BitSet r){
        //TODO: verify that the bitset r does not delete what was at node.getState()
        if(a.isNondeterministic){
            VEffect e = a.getEffects().get(node.indexEffect);
            /*if(e.getCondition() != null) {
                //for (int c : e.getCondition()) r.set(c);
                //Add operation between bitsets:
                r.or(e.getCondition());
            }*/
            //BitSet A = (BitSet) e.getAddList().clone();
            //A.and(r);
            /*if(A.equals(e.getAddList())){

            }*/
            r.or(e.getCondition());
            for(int j = e.getAddList().nextSetBit(0); j>=0;j=e.getAddList().nextSetBit(j+1)){
                //TODO: vvvv verify regression here! vvvvv
                if(!node.parent.getState().get(j)){
                    r.set(j,false);
                }
                //r.set(j,false);
            }
        }else{
            for(VEffect e : a.getEffects()){
                //for(int c : e.getCondition()) r.set(c);
                //Verify the effect was applied:
                if(e.getCondition().isEmpty()){
                    for(int j = e.getAddList().nextSetBit(0); j>=0;j=e.getAddList().nextSetBit(j+1)){
                        //TODO: vvvv verify regression here! vvvvv
                        if(!node.parent.getState().get(j)){
                            r.set(j,false);
                        }
                        //r.set(j,false);
                    }
                }else{
                    BitSet A = (BitSet) e.getAddList().clone();
                    A.and(r);
                    if(A.equals(e.getAddList())){
                        r.or(e.getCondition());
                    }
                }
            }
        }
    }

    private void printPlan(Node node) {
        System.out.println("Printing solution:");
        ArrayList<String> solution = new ArrayList<String>();
        while(node.parent != null){
            solution.add(node.parentAction);
            node = node.parent;
        }
        for(int i = solution.size(); i>0; i--){
            System.out.println(solution.get(i-1));
        }
    }

    private boolean visited(Node node) {
        return visited.contains(node.getState());
    }

    private ArrayList<VAction> getApplicableActions(Node node) {
        //System.out.println("Applicable actions in: " + problem.printState(node.getState()));
        ArrayList<VAction> retList = new ArrayList<VAction>();
        /*problem.getVaList().stream()
                .filter(s -> ((s.getName().s) && (node.holds(s.getPreconditionArray()))))
                .forEach(retList::add);*/
        for(VAction va : problem.getVaList()){
        	if(va.getName().startsWith("invariant-at") || forbiddenHelp.get(va.index) || forbiddenActions.get(va.index)) continue;
            //if(node.holds(va.getPreconditionArray())){
            if(node.holds(va.getPreconditions())){
                retList.add(va);
                //System.out.println(va.getName());
            }

        }
        return retList;
    }
}
