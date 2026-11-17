module

public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Data.Matrix.Basic
public import Class.Data.Set.Add
public import Class.Data.Nat.GCD.Intfunc
public import Class.Probability.Process.StochasticProcessTypes.Part2

@[expose] public section

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


-- step counts at which a tag/state i can recur with positive probability in sequence-modeling tasks
noncomputable def return_times {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] (i : S) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ 0 < (P ^ n) i i}

