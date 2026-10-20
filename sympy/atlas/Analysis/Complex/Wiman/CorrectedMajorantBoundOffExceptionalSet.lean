/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CorrectedMajorantBoundOffExceptionalSet.lean -/

import sympy.atlas.Analysis.Complex.Wiman.CorrectedRosenbloom
import sympy.atlas.Analysis.Complex.Wiman.TwoPowerBadSets
namespace Complex

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Outside a finite exceptional set, the radial majorant is controlled by the maximum term and
the specialized power of the logarithmic majorant. -/
theorem wimanMajorant_bound_off_exceptionalSet
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) :
    ∃ C x₀ : ℝ, 0 < C ∧
      volume (wimanExceptionalSet f x₀) < ∞ ∧
      ∀ x, x₀ ≤ x → x ∉ wimanExceptionalSet f x₀ →
        wimanMajorant f (Real.exp x) ≤
          C * wimanMaximumTerm f (Real.exp x) *
            (1 + wimanGrowth f x ^ (81 / 128 : ℝ)) := by
  obtain ⟨xE, hEfinite, hEbound⟩ :=
    exists_finite_wimanExceptionalSet f hf htrans
  obtain ⟨xP, hpos, _, _, _, _⟩ := eventually_wimanGrowth_regular f hf htrans
  let x₀ : ℝ := max xE xP
  have hxE : xE ≤ x₀ := le_max_left _ _
  have hxP : xP ≤ x₀ := le_max_right _ _
  have hExceptionalSubset :
      wimanExceptionalSet f x₀ ⊆ wimanExceptionalSet f xE := by
    intro x hx
    simp only [wimanExceptionalSet, Real.powerGrowthBadSet, mem_union, mem_ofPred_eq] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl ⟨hxE.trans hx.1, hx.2⟩
    · exact Or.inr ⟨hxE.trans hx.1, hx.2⟩
  have hfinite : volume (wimanExceptionalSet f x₀) < ∞ :=
    measure_lt_top_mono hExceptionalSubset hEfinite
  refine ⟨8, x₀, by norm_num, hfinite, ?_⟩
  intro x hx hxgood
  have hxgoodE : x ∉ wimanExceptionalSet f xE := by
    intro hbad
    apply hxgood
    simp only [wimanExceptionalSet, Real.powerGrowthBadSet, mem_union, mem_ofPred_eq] at hbad ⊢
    rcases hbad with hbad | hbad
    · exact Or.inl ⟨hx, hbad.2⟩
    · exact Or.inr ⟨hx, hbad.2⟩
  have hsecond :
      iteratedDeriv 2 (wimanGrowth f) x ≤
        wimanGrowth f x ^ (81 / 64 : ℝ) :=
    hEbound x (hxE.trans hx) hxgoodE
  have hgx : 0 < wimanGrowth f x := hpos x (hxP.trans hx)
  have hsqrt :
      Real.sqrt (wimanGrowth f x ^ (81 / 64 : ℝ)) =
        wimanGrowth f x ^ (81 / 128 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hgx.le]
    congr 1
    norm_num
  have hmaximumNonneg : 0 ≤ wimanMaximumTerm f (Real.exp x) :=
    (wimanTerm_nonneg f (Real.exp x) 0).trans
      (wimanTerm_le_wimanMaximumTerm f hf (Real.exp x) 0)
  calc
    wimanMajorant f (Real.exp x) ≤
        8 * wimanMaximumTerm f (Real.exp x) *
          (1 + Real.sqrt (iteratedDeriv 2 (wimanGrowth f) x)) :=
      wimanMajorant_le_eight_mul_maximumTerm f hf x
    _ ≤ 8 * wimanMaximumTerm f (Real.exp x) *
          (1 + Real.sqrt (wimanGrowth f x ^ (81 / 64 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right (Real.sqrt_le_sqrt hsecond) 1)
        (mul_nonneg (by norm_num) hmaximumNonneg)
    _ = 8 * wimanMaximumTerm f (Real.exp x) *
          (1 + wimanGrowth f x ^ (81 / 128 : ℝ)) := by
      rw [hsqrt]

end
