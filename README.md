# We used the SAT to model the SAT
DPLL/CDCL modelled in Forge. Created by Matt Shinkar, Derick Toth, and Nick Young

## TODO:
- Finish CDCL
- Better visualizations
- Fix this README; add CDCL stuff
- Handin!

## Overview

This is a Forge/Electrum model of DPLL/CDCL. In this repo, you'll find three subfolders: `naive_dpll`, `better_dpll`, and `cdcl`. The `naive_dpll` folder contains our first attempt at modelling the algorithm - it is a very naive approach that has nothing but backtracking, and no further optimizations. The `better_dpll` folder contains a full DPLL model, complete with unit clause propagation and pure literal elimation. The `cdcl` folder contains a CDCL model, which supports BCP and nonchronological backtracking - it was also our reach goal!

Each folder contains its own visualizer - to run it, use the "Script" tab in Sterling, open the corresponding visualizer file in `<div>` mode, and execute. Stepping through the timesteps will update the visualization to reflect the state of the model.

There is also a Python script, `generate.py`, that takes in a DIMACS CNF file and prints out a Forge-parsable instance. This is useful for testing out a known trace.


## Questions

**What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?**

In DPLL, we forced variable choices to always be True, then False, which made it easier to maintain when we were finished with our search, but made it difficult to have any heuristic (we didn't have any intelligent heuristics). We also had issues deciding how to model backtracking - we decided on using a stack to maintain a structural representation of the actual stack trace created in recursion, but also tried out other structures, like trees.


**What assumptions did you make about scope? What are the limits of your model?**

We knew going into this that the instances we could actually solve were quite limited. We also knew it would be difficult to employ any heuristics - as such, we scoped our project to model base DPLL - no optimizations beyond unit clause propagation and pure literal elimation. Our model is slow on large instances and can't handle overly large trace lengths. However, it is otherwise pretty robusts!


**Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?**

We were able to meet all of our goals from the proposal.


**How should we understand an instance of your model and what your custom visualization shows?**

Each instance of our model is a generated set of clauses, and the trace is the steps that DPLL/CDCL takes in determining whether or not this set of clauses is satisfiable. Each timestep might be making a guess, backtracking, applying unit clause propagation, etc.

The DPLL visualizations will show the current instance's clauses above the hline, and the current timestep's assigned literals (black) and implied literals (red, learned from unit clause/pure literal) under the hline.
