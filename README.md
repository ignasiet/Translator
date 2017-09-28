# Translator
Implementation of different algorithms to deal with Contingent Planning problems.
These algorithms translate the original problem to an *epistemic* version.
The translations are based on the work of Albore, Bonet, Geffner and Palacios.

Algorithms implemented: PRP (Muise et al. 2012).

Known bugs:
* Pddl problem files: the :init must start with a list, for example (:init **(and** .... **)** ), otherwise it does not read the initial state correctly.
