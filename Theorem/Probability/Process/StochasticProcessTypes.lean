module

public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Data.Matrix.Basic
public import Class.Data.Set.Add
public import Class.Data.Nat.GCD.Intfunc
public import Instance.Probability.Process.StochasticProcessTypes.Part2
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


-- probability of an m+n-step i→j path is at least the product of an m-step i→k
-- path and an n-step k→j path (all other decompositions are nonneg)
public section

theorem get_pow_add_ge_mul_get_s_pow {S : Type u} [Fintype S] [DecidableEq S]
    {P : Matrix S S ℝ} [RowStochastic P] (m n : ℕ) (i j k : S) :
    (P ^ (m + n)) i j ≥ (P ^ m) i k * (P ^ n) k j := by
  have := smat_pow_is_smat (P := P) m
  have := smat_pow_is_smat (P := P) n
  rw [pow_add]
  simp [Matrix.mul_apply]
  rw [← Finset.sum_erase_add (a := k)]
  · apply le_add_of_nonneg_left
    apply Finset.sum_nonneg
    intro l hl
    apply mul_nonneg <;>
      apply (RowStochastic.stochastic _).nonneg
  · simp
