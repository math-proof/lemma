import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic
import Class.Data.Set.Add
import Class.Data.Nat.GCD.Intfunc
import Abbrev.Probability.Process.StochasticProcessTypes.Part3
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


-- result of composing two tag-transition matrices is still a valid transition matrix
instance smat_mul_smat_is_smat {S : Type u} [Fintype S]
    (P Q : Matrix S S ℝ) [hP : RowStochastic P] [hQ : RowStochastic Q] :
    RowStochastic (P * Q) where
  stochastic i := by
    refine ⟨?nonneg, ?rowsum⟩
    · intro j
      have : 0 ≤ ∑ k, P i k * Q k j :=
        sum_nonneg fun k _ =>
          mul_nonneg (hP.stochastic i |>.nonneg k) (hQ.stochastic k |>.nonneg j)
      simpa [Matrix.mul_apply] using this
    · calc
          ∑ j, (P * Q) i j
        _ = ∑ j, ∑ k, P i k * Q k j := by simp [Matrix.mul_apply]
        _ = ∑ k, ∑ j, P i k * Q k j := by rw [sum_comm]
        _ = ∑ k, P i k * ∑ j, Q k j := by
            apply sum_congr rfl; intro k _; simp [mul_sum]
        _ = ∑ k, P i k := by
            apply sum_congr rfl; intro k _; simp [(hQ.stochastic k).rowsum]
        _ = 1 := (hP.stochastic i).rowsum

instance smat_pow_is_smat {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ) : RowStochastic (P ^ n) := by
  induction n with
  | zero =>
    refine ⟨fun i => ⟨?_, ?_⟩⟩
    · intro j
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    · simp [Matrix.one_apply]
  | succ n ih =>
    have := ih
    simpa [pow_succ] using smat_mul_smat_is_smat (P ^ n) P

