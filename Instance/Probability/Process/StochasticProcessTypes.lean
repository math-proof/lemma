module

public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Data.Matrix.Basic
public import Class.Data.Set.Add
public import Class.Data.Nat.GCD.Intfunc
public import Class.Probability.Process.StochasticProcessTypes.Part3

/-!
# Stochastic process types (DiscreteMarkovChain)

Finite discrete-time homogeneous Markov-chain primitives, aligned with
[Instance.Probability.Process.StochasticProcessTypes.Part3.DiscreteMarkovChain](https://github.com/sympy/sympy/blob/master/sympy/stats/stochastic_process_types.py).

In Lean these are typeclasses on a transition matrix `P : Matrix S S ℝ`
(`RowStochastic`, `StochasticIrreducible`, `Aperiodic`) plus the probability
simplex `StochasticVec` / `Simplex`, rather than a single Python class.
-/

@[expose] public section

open Finset Matrix WithLp Set
open scoped Matrix BigOperators

universe u

instance {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] [Aperiodic P] (i : S) :
    FiniteGCDOne (return_times P i) :=
  Aperiodic.aperiodic (P := P) i
