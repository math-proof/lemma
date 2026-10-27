import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic
import Class.Data.Set.Add
import Class.Data.Nat.GCD.Intfunc
import Def.Probability.Process.StochasticProcessTypes
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


-- no fixed period for revisiting a tag/state (useful so long tag sequences are not stuck on even/odd steps, etc.)
class Aperiodic {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] : Prop where
  aperiodic : ∀ i, FiniteGCDOne (return_times P i)

