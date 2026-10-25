import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Shearer
open Finset Real BigOperators Shearer


namespace Shearer

/--
[entropy_subadditive_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Shearer.lean)
-/
@[path]
lemma entropy_subadditive_two
  [Fintype β]
  [Fintype γ]
  {q : β × γ → ℝ}
-- given
  (hq_nn : ∀ x, 0 ≤ q x)
  (hq_sum : ∑ x : β × γ, q x = 1) :
-- imply
  ∑ x : β × γ, negMulLog (q x) ≤ ∑ b : β, negMulLog (∑ c : γ, q (b, c)) + ∑ c : γ, negMulLog (∑ b : β, q (b, c)) := by
-- proof
  set qβ : β → ℝ := fun b => ∑ c : γ, q (b, c)
  set qγ : γ → ℝ := fun c => ∑ b : β, q (b, c)
  have hqβ_nn : ∀ b, 0 ≤ qβ b := fun b => Finset.sum_nonneg (fun c _ => hq_nn (b, c))
  have hqβ_sum : ∑ b, qβ b = 1 := by
    simp only [qβ]; rw [← hq_sum]; exact (Fintype.sum_prod_type (f := q)).symm
  have hq_le_qβ : ∀ b c, q (b, c) ≤ qβ b :=
    fun b c => Finset.single_le_sum (fun c' _ => hq_nn (b, c')) (Finset.mem_univ c)
  have hmul_div : ∀ b c, qβ b * (q (b, c) / qβ b) = q (b, c) := by
    intro b c
    obtain h0 | hpos := eq_or_lt_of_le (hqβ_nn b)
    · have hbc : q (b, c) = 0 := le_antisymm (by linarith [hq_le_qβ b c]) (hq_nn (b, c))
      simp [← h0, hbc]
    · exact mul_div_cancel₀ (q (b, c)) (ne_of_gt hpos)
  have hdiv_nn : ∀ b c, 0 ≤ q (b, c) / qβ b := fun b c => div_nonneg (hq_nn (b, c)) (hqβ_nn b)
  have hJensen_c : ∀ c, ∑ b, qβ b * negMulLog (q (b, c) / qβ b) ≤ negMulLog (qγ c) := by
    intro c
    have hJ := concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := qβ) (p := fun b => q (b, c) / qβ b)
      (fun b _ => hqβ_nn b) (by simp [hqβ_sum]) (fun b _ => Set.mem_Ici.mpr (hdiv_nn b c))
    simp only [smul_eq_mul] at hJ
    have heq : ∑ b, qβ b * (q (b, c) / qβ b) = qγ c := by simp_rw [hmul_div]; rfl
    rw [heq] at hJ; exact hJ
  have hkey : ∑ c, ∑ b, qβ b * negMulLog (q (b, c) / qβ b) ≤ ∑ c, negMulLog (qγ c) :=
    Finset.sum_le_sum (fun c _ => hJensen_c c)
  have hdecomp : ∑ x : β × γ, negMulLog (q x) =
    ∑ b, negMulLog (qβ b) + ∑ c, ∑ b, qβ b * negMulLog (q (b, c) / qβ b) := by
    rw [Fintype.sum_prod_type]
    conv_rhs => rw [Finset.sum_comm (f := fun c b => qβ b * negMulLog (q (b, c) / qβ b))]
    simp_rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b _
    have hterms : ∀ c, negMulLog (q (b, c)) =
      (q (b, c) / qβ b) * negMulLog (qβ b) + qβ b * negMulLog (q (b, c) / qβ b) := by
      intro c; conv_lhs => rw [← hmul_div b c]; exact negMulLog_mul (qβ b) (q (b, c) / qβ b)
    simp_rw [hterms, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    congr 1
    obtain h0 | hpos := eq_or_lt_of_le (hqβ_nn b)
    · simp [← h0, show ∀ c, q (b, c) = 0 from fun c =>
      le_antisymm (by linarith [hq_le_qβ b c]) (hq_nn (b, c))]
    · have hsd : ∑ c : γ, q (b, c) / qβ b = 1 := by
      rw [← Finset.sum_div, div_self (ne_of_gt hpos)]
      rw [hsd, one_mul]
  linarith [hdecomp, hkey]

end Shearer

namespace Shearer

/--
[cond_sub_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Shearer.lean)
-/
@[path]
lemma cond_sub_pointwise
  [Fintype β]
  [Fintype γ]
  {f : β × γ → ℝ}
  {m : ℝ}
-- given
  (hf_nn : ∀ x, 0 ≤ f x)
  (hm_nn : 0 ≤ m)
  (hf_sum : ∑ x : β × γ, f x = m) :
-- imply
  ∑ x : β × γ, negMulLog (f x) + negMulLog m ≤ ∑ b : β, negMulLog (∑ c : γ, f (b, c)) + ∑ c : γ, negMulLog (∑ b : β, f (b, c)) := by
-- proof
  obtain hm0 | hm_pos := eq_or_lt_of_le hm_nn
  · have hf_zero : ∀ x, f x = 0 := by
    intro x
    have h1 : f x ≤ ∑ y : β × γ, f y :=
      Finset.single_le_sum (fun y _ => hf_nn y) (Finset.mem_univ x)
    linarith [hf_nn x]
    simp [hf_zero, ← hm0]
  · set q : β × γ → ℝ := fun x => f x / m
    have hq_nn : ∀ x, 0 ≤ q x := fun x => div_nonneg (hf_nn x) (le_of_lt hm_pos)
    have hq_sum : ∑ x : β × γ, q x = 1 := by
      simp only [q, ← Finset.sum_div, hf_sum, div_self (ne_of_gt hm_pos)]
    have hsub := entropy_subadditive_two q hq_nn hq_sum
    have hfq : ∀ x, f x = m * q x := by
      intro x; simp [q, mul_div_cancel₀ (f x) (ne_of_gt hm_pos)]
    have hLHS : ∑ x : β × γ, negMulLog (f x) + negMulLog m =
      2 * negMulLog m + m * ∑ x, negMulLog (q x) := by
      have hdecomp_f : ∀ x, negMulLog (f x) = q x * negMulLog m + m * negMulLog (q x) := by
        intro x; rw [hfq]; exact negMulLog_mul m (q x)
      simp_rw [hdecomp_f, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq_sum]
      ring
    have hRHS : ∑ b, negMulLog (∑ c : γ, f (b, c)) + ∑ c, negMulLog (∑ b : β, f (b, c)) =
      2 * negMulLog m + m * (∑ b, negMulLog (∑ c, q (b, c)) + ∑ c, negMulLog (∑ b, q (b, c))) := by
      have hmarg_b : ∀ b, ∑ c : γ, f (b, c) = m * ∑ c : γ, q (b, c) := by
        intro b; simp_rw [hfq]; rw [← Finset.mul_sum]
      have hmarg_c : ∀ c, ∑ b : β, f (b, c) = m * ∑ b : β, q (b, c) := by
        intro c; simp_rw [hfq]; rw [← Finset.mul_sum]
      simp_rw [hmarg_b, hmarg_c, negMulLog_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
      have hsum_bc : ∑ b : β, ∑ c : γ, q (b, c) = 1 := by
        rw [← Fintype.sum_prod_type (f := q)]; exact hq_sum
      have hsum_cb : ∑ c : γ, ∑ b : β, q (b, c) = 1 := by
        rw [Finset.sum_comm, ← Fintype.sum_prod_type (f := q)]; exact hq_sum
      rw [hsum_bc, hsum_cb]; ring
    rw [hLHS, hRHS]
    linarith [mul_le_mul_of_nonneg_left hsub (le_of_lt hm_pos)]

end Shearer

namespace Shearer

/--
[entropy_cond_sub_marginal1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Shearer.lean)
-/
@[path]
lemma entropy_cond_sub_marginal1
  [Fintype α]
  [Fintype β]
  [Fintype γ]
  {p : α × β × γ → ℝ}
-- given
  (hp_nn : ∀ x, 0 ≤ p x)
  (hp_sum : ∑ x : α × β × γ, p x = 1) :
-- imply
  entropy p + entropy (marginal1 p) ≤ entropy (marginal12 p) + entropy (marginal13 p) := by
-- proof
  unfold entropy marginal1 marginal12 marginal13
  rw [show ∑ x : α × β × γ, negMulLog (p x) =
    ∑ a : α, ∑ bc : β × γ, negMulLog (p (a, bc)) from Fintype.sum_prod_type _]
  rw [show ∑ x : α × β, negMulLog (∑ c : γ, p (x.1, x.2, c)) =
    ∑ a : α, ∑ b : β, negMulLog (∑ c : γ, p (a, b, c)) from Fintype.sum_prod_type _]
  rw [show ∑ x : α × γ, negMulLog (∑ b : β, p (x.1, b, x.2)) =
    ∑ a : α, ∑ c : γ, negMulLog (∑ b : β, p (a, b, c)) from Fintype.sum_prod_type _]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro a _
  have hfa_nn : ∀ x : β × γ, 0 ≤ p (a, x) := fun x => hp_nn (a, x)
  have hma_nn : 0 ≤ ∑ b : β, ∑ c : γ, p (a, b, c) :=
    Finset.sum_nonneg (fun b _ => Finset.sum_nonneg (fun c _ => hp_nn (a, b, c)))
  have hfa_sum : ∑ x : β × γ, p (a, x) = ∑ b : β, ∑ c : γ, p (a, b, c) :=
    Fintype.sum_prod_type _
  rw [show ∑ bc : β × γ, negMulLog (p (a, bc)) = ∑ x : β × γ, negMulLog (p (a, x)) from rfl]
  exact cond_sub_pointwise (fun x => p (a, x)) hfa_nn hma_nn hfa_sum
/-- Conditional subadditivity around the second variable: $H(X,Y,Z) + H(Y) \le H(X,Y) + H(Y,Z)$. -/

end Shearer


-- created on 2026-10-23
