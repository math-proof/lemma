import sympy.stats.markov_reward_process
import sympy.Basic
open Matrix Finset MeasureTheory ProbabilityTheory


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {MRP : FiniteMRP S}
  {n : ℕ}
-- given
  (h : 1 ≤ n)
  (y z : S × S) :
-- imply
  (MRP.aug_chain_markov.kernel_mat ^ n) y z = (MRP.P ^ (n - 1)) y.2 z.1 * MRP.P z.1 z.2 := by
-- proof
  have hP : RowStochastic MRP.P := inferInstance
  have h₁ : ∀ y z : S × S, MRP.aug_chain_markov.kernel_mat y z = if y.2 = z.1 then MRP.P z.1 z.2 else 0 := by
    intro y z
    simp only [HomMarkovChainSpec.kernel_mat, FiniteMRP.aug_chain_markov, Kernel.ofFunOfCountable, Matrix.of_apply]
    rw [Kernel.coe_mk, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z), PMF.ofFintype_apply,
      ENNReal.toReal_ofReal]
    split_ifs
    · exact (hP.stochastic z.1).nonneg z.2
    · exact le_rfl
  induction n, h using Nat.le_induction generalizing y z with
  | base =>
    rw [pow_one, h₁, Nat.sub_self, pow_zero, one_apply]
    split_ifs <;> simp
  | succ n hn ih =>
    rw [pow_succ, mul_apply, Fintype.sum_prod_type]
    simp only [ih, h₁, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, show m + 1 + 1 - 1 = m + 1 by omega, pow_succ, mul_apply, sum_mul]


-- created on 2026-09-26