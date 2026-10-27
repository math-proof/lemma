import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic
import Class.Data.Set.Add
import Class.Data.Nat.GCD.Intfunc
import Abbrev.Probability.Process.StochasticProcessTypes.Part2
open Finset Matrix WithLp Set
open scoped Matrix BigOperators

universe u

/-!
# Stochastic process types (DiscreteMarkovChain)

Empty.Finite discrete-time homogeneous Markov-chain primitives, aligned with
[Instance.Probability.Process.StochasticProcessTypes.Part3.DiscreteMarkovChain](https://github.com/sympy/sympy/blob/master/sympy/stats/stochastic_process_types.py).

In Lean these are typeclasses on a transition matrix `P : Matrix S S ℝ`
(`RowStochastic`, `StochasticIrreducible`, `Aperiodic`) plus the probability
simplex `StochasticVec` / `Simplex`, rather than a single Python class.
-/


-- asserts that P is a Markov transition matrix, wherein P i j is the probability of going from current tag/state i to next tag/state j in one step.
class RowStochastic {S : Type u} [Fintype S] (P : Matrix S S ℝ) : Prop where
  stochastic : ∀ s, StochasticVec (P s)

-- assumes every state can reach every other with positive probability in finite steps
class StochasticIrreducible {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] : Prop where
  irreducible : ∀ i j, ∃ n : ℕ, 0 < (P ^ n) i j

