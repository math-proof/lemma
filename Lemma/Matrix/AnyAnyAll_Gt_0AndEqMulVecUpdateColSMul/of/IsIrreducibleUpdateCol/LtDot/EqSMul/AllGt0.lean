import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Lemma.Matrix.Any_Gt_0AndAny_All_Gt_0AndEqMulVecSMul.of.All_Any_GtGetPow_0.All_Ge_0
import Lemma.Matrix.Any_Gt_0AndAny_All_Gt_0AndEqVecMulSMul.of.All_Any_GtGetPow_0.All_Ge_0
import Lemma.Matrix.Lt.of.MulVec.eq.SMul.LtDot.All_Eq.EqSMul.GtNeg1.GtNeg1.AllGt0.AllGt0
import sympy.Basic

open Matrix
open scoped Matrix

@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {M : Matrix S S ℝ}
  {p v : S → ℝ}
  {r : ℝ}
  {i : S}
-- given
  (hp : ∀ k, 0 < p k)
  (hM : (1 + r) • (p ᵥ* M) = p)
  (hi : p ⬝ᵥ v < p ⬝ᵥ (fun k => M k i))
  (h : (M.updateCol i v).IsIrreducible) :
-- imply
  ∃ r' > r, ∃ p' : S → ℝ, (∀ k, 0 < p' k) ∧ (1 + r') • (p' ᵥ* M.updateCol i v) = p' := by
-- proof
  have : Nonempty S := ⟨i⟩
  have hv : 0 ≤ p ⬝ᵥ v := by
    apply Finset.sum_nonneg
    intro k _
    have := h.nonneg k i
    simp at this
    exact mul_nonneg (hp k).le this
  have hr : -1 < r := by
    have h₀ := congrFun hM i
    have h₁ : 0 < (p ᵥ* M) i := hv.trans_lt hi
    simp only [Pi.smul_apply, smul_eq_mul] at h₀
    nlinarith [hp i]
  obtain ⟨l, hl, q, hq, h₂⟩ := Any_Gt_0AndAny_All_Gt_0AndEqMulVecSMul.of.All_Any_GtGetPow_0.All_Ge_0 h.nonneg ((isIrreducible_iff_exists_pow_pos h.nonneg).1 h)
  have h₃ : 0 < 1 / l := one_div_pos.2 hl
  have h₄ : 1 / (1 + (1 / l - 1)) = l := by simp
  have h₅ : M.updateCol i v *ᵥ q = (1 / (1 + (1 / l - 1))) • q := by rwa [h₄]
  have h₆ : M.updateCol i v *ᵥ q = l • q := by rwa [h₄] at h₅
  obtain ⟨l2, hl2, p', hp', h₇⟩ := Any_Gt_0AndAny_All_Gt_0AndEqVecMulSMul.of.All_Any_GtGetPow_0.All_Ge_0 h.nonneg ((isIrreducible_iff_exists_pow_pos h.nonneg).1 h)
  have hpq : 0 < p' ⬝ᵥ q := Finset.sum_pos (fun k _ => mul_pos (hp' k) (hq k)) Finset.univ_nonempty
  have h₈ : l2 * (p' ⬝ᵥ q) = l * (p' ⬝ᵥ q) := by
    calc l2 * (p' ⬝ᵥ q) = (l2 • p') ⬝ᵥ q := by rw [smul_dotProduct, smul_eq_mul]
      _ = (p' ᵥ* M.updateCol i v) ⬝ᵥ q := by rw [h₇]
      _ = p' ⬝ᵥ (M.updateCol i v *ᵥ q) := by rw [Matrix.dotProduct_mulVec]
      _ = p' ⬝ᵥ (l • q) := by rw [h₆]
      _ = l * (p' ⬝ᵥ q) := by rw [dotProduct_smul, smul_eq_mul]
  have h₉ : l2 = l := mul_right_cancel₀ hpq.ne' h₈
  have h₁₀ : (1 + (1 / l - 1)) * l = 1 := by
    rw [show 1 + (1 / l - 1) = 1 / l by ring]
    exact one_div_mul_cancel hl.ne'
  refine ⟨1 / l - 1, ?_, p', hp', ?_⟩
  · exact Lt.of.MulVec.eq.SMul.LtDot.All_Eq.EqSMul.GtNeg1.GtNeg1.AllGt0.AllGt0 (i := i) hp hq hr (by linarith) hM (fun j hj k => by simp [Matrix.updateCol_ne hj]) (by simpa using hi) h₅
  · rw [h₇, h₉, smul_smul, h₁₀, one_smul]


-- created on 2026-09-29