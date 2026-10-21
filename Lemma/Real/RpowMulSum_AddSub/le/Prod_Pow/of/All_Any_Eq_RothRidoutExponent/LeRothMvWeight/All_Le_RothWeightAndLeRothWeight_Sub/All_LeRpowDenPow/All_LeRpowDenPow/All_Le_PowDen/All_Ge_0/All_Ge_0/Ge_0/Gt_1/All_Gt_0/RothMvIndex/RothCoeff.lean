import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Real.RpowMulAddSub.le.Pow_RothRidoutExponent.of.In_SupportRothMvHasse_RothMvOfCoeff.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_Le_PowDen.Ge_0.Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff
open MathlibExt.NumberTheory.RothAuxiliary
open Real


/--
[roth_ridout_common_divisor_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (S : Finset ι)
  (p : ι → ℕ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (a b : Fin m → ι → ℕ)
  (μ ν : ι → ℝ)
  (c : RothCoeff r)
  (Q T θ : ℝ)
  (i : RothMvIndex m)
  (e : ι → ℕ)
-- given
  (hr : ∀ h, 0 < r h)
  (hQ : 1 < Q)
  (hθ : 0 ≤ θ)
  (hμ : ∀ l ∈ S, 0 ≤ μ l)
  (hν : ∀ l ∈ S, 0 ≤ ν l)
  (hpower : ∀ h, Q ≤ ((q h).den : ℝ) ^ r h)
  (ha : ∀ h l, l ∈ S →
    Real.rpow ((q h).den : ℝ) (μ l) ≤ (p l : ℝ) ^ a h l)
  (hb : ∀ h l, l ∈ S →
    Real.rpow ((q h).den : ℝ) (ν l) ≤ (p l : ℝ) ^ b h l)
  (hbalanced : ∀ j, c j ≠ 0 →
    T ≤ rothWeight r (fun h ↦ j h) ∧
      rothWeight r (fun h ↦ j h) ≤ (m : ℝ) - T)
  (hi : rothMvWeight r i ≤ θ)
  (hmin : ∀ l ∈ S, ∃ k ∈ (rothMvHasse i (rothMvOfCoeff c)).support,
    e l = rothRidoutExponent r a b k l) :
-- imply
  Real.rpow Q ((∑ l ∈ S, (μ l + ν l)) * (T - θ)) ≤
    ((∏ l ∈ S, p l ^ e l : ℕ) : ℝ) := calc
    _ = ∏ l ∈ S, Real.rpow Q ((μ l + ν l) * (T - θ)) := by
      rw [Finset.sum_mul]
      exact Real.rpow_sum_of_pos (by linarith) _ S
    _ ≤ ∏ l ∈ S, (p l : ℝ) ^ e l := by
      apply Finset.prod_le_prod₀
      ·
        intro l _
        exact Real.rpow_nonneg (by linarith) _
      ·
        intro l hl
        obtain ⟨k, hk, hek⟩ := hmin l hl
        simpa [hek] using
          RpowMulAddSub.le.Pow_RothRidoutExponent.of.In_SupportRothMvHasse_RothMvOfCoeff.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_Le_PowDen.Ge_0.Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff
            p q r a b μ ν c Q T θ l i k
            hr hQ hθ (hμ l hl) (hν l hl) hpower
            (fun h ↦ ha h l hl) (fun h ↦ hb h l hl) hbalanced hi hk
    _ = ((∏ l ∈ S, p l ^ e l : ℕ) : ℝ) := by
      push_cast
      rfl


-- created on 2026-10-21
