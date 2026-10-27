import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic
import Class.Data.Set.Add
import Class.Data.Nat.GCD.Intfunc
import Theorem.Probability.Process.StochasticProcessTypes
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


-- return times are closed under addition: positive i→i paths of lengths a and b
-- concatenate into a positive i→i path of length a + b
instance return_times_closedUnderAdd {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] (i : S) :
    ClosedUnderAdd (return_times P i) where
  closed_under_add a b ha hb := by
    simp only [return_times, Set.mem_ofPred_eq] at ha hb ⊢
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨by linarith, ?_⟩
    calc
      _ < (P ^ a) i i * (P ^ b) i i := mul_pos ha2 hb2
      _ ≤ (P ^ (a + b)) i i :=
          (get_pow_add_ge_mul_get_s_pow (P := P) a b i i i).le

instance svec_mul_smat_is_svec {S : Type u} [Fintype S]
    (μ : S → ℝ) [hμ : StochasticVec μ] (P : Matrix S S ℝ) [hP : RowStochastic P] :
    StochasticVec (μ ᵥ* P) where
  nonneg j := by
    have : 0 ≤ ∑ i, μ i * P i j :=
      sum_nonneg fun i _ => mul_nonneg (hμ.nonneg i) ((hP.stochastic i).nonneg j)
    simpa [Matrix.vecMul, dotProduct] using this
  rowsum := by
    change ∑ j, ∑ i, μ i * P i j = 1
    rw [sum_comm]
    calc
        ∑ i, ∑ j, μ i * P i j
      _ = ∑ i, μ i * ∑ j, P i j := by
          apply sum_congr rfl; intro i _; rw [← mul_sum]
      _ = ∑ i, μ i := by
          apply sum_congr rfl; intro i _; rw [(hP.stochastic i).rowsum, mul_one]
      _ = 1 := hμ.rowsum

-- uniform_distribution is always stochastic
instance uniform_distribution_stochastic {S : Type u} [Fintype S] [Nonempty S] :
    StochasticVec (S := S) uniform_distribution where
  nonneg s := by simp [uniform_distribution]
  rowsum := by
    simp [uniform_distribution, Finset.sum_const, Finset.card_univ]

