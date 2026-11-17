module

public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Data.Matrix.Basic
public import Class.Data.Set.Add
public import Class.Data.Nat.GCD.Intfunc
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


-- L1 space over S (typically, Fin n)
abbrev l1Space (S : Type u) := WithLp 1 (S → ℝ)

-- reinterpret a score vector as a point of l1Space
noncomputable abbrev ofL1 {S : Type u} (x : S → ℝ) : l1Space S :=
  (WithLp.equiv 1 (S → ℝ)).symm x

