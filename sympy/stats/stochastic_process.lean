import sympy.stats.stochastic_process_types
import sympy.stats.stochastic_process_topology
import sympy.stats.stochastic_process_operator
import sympy.stats.stochastic_process_minorization
import sympy.stats.stochastic_process_stationary
import sympy.stats.stochastic_process_mixing

/-!
# Stochastic processes

Entry point aligned with
[sympy.stats.stochastic_process](https://github.com/sympy/sympy/blob/master/sympy/stats/stochastic_process.py)
and the `DiscreteMarkovChain` exports from `stochastic_process_types`.

Import this module for the Markov-chain typeclasses; detailed topology,
contraction, minorization, and stationary/mixing results live in the sibling
`stochastic_process_*` modules.
-/

open StochasticMatrix
