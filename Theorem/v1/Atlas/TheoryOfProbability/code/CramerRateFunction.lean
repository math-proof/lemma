/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/CramerRateFunction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Semicontinuity.Basic
import Def.ProbabilityTheory.CramerTheorem
import Def.ProbabilityTheory.LegendreTransform
import Structure.v1.Atlas.TheoryOfProbability.code.LargeDeviations
open MeasureTheory ProbabilityTheory Real
open scoped InnerProductSpace ENNReal Topology


/-- The real log-MGF vanishes at the origin on a probability space. -/
theorem logMGFVec_zero {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    logMGFVec X μ 0 = 0 := by
  simp [logMGFVec]

/-- Constant vectors have log-MGF equal to the inner product. -/
theorem logMGFVec_const {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (c : EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : EuclideanSpace ℝ (Fin d)) :
    logMGFVec (fun _ => c) μ t = ⟪t, c⟫_ℝ := by
  simp [logMGFVec, integral_const, Measure.real]

/-- The vector log-MGF of the identity map is the log of the Laplace transform. -/
theorem logMGFVec_id {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) (t : EuclideanSpace ℝ (Fin d)) :
    logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t =
      log (∫ x, exp (⟪t, x⟫_ℝ) ∂μ₀) :=
  rfl

/-- Pushing a random vector forward preserves its log-MGF. -/
theorem logMGFVec_eq_logMGFVec_id_map {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω)
    (t : EuclideanSpace ℝ (Fin d)) (hX : AEMeasurable X μ) :
    logMGFVec X μ t =
      logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) (μ.map X) t := by
  simp only [logMGFVec, logMGFVec_id]
  have hfm : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin d) => exp (⟪t, x⟫_ℝ))
      (μ.map X) :=
    (continuous_exp.comp (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) =>
      ⟪t, x⟫_ℝ)).aestronglyMeasurable
  rw [integral_map hX hfm]

/-- Fenchel–Young for the real Legendre transform, under a bounded-above hypothesis. -/
theorem le_legendreTransform {d : ℕ} (Λ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x l : EuclideanSpace ℝ (Fin d))
    (hbdd : BddAbove (Set.range fun y => ⟪y, x⟫_ℝ - Λ y)) :
    ⟪l, x⟫_ℝ - Λ l ≤ legendreTransform Λ x :=
  le_ciSup hbdd l

/-- Under probability, the Legendre transform of `logMGFVec` is nonnegative when the
supporting values are bounded above (so the real `iSup` is a true supremum). -/
theorem legendreTransform_logMGFVec_nonneg {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : EuclideanSpace ℝ (Fin d))
    (hbdd : BddAbove (Set.range fun t => ⟪t, x⟫_ℝ - logMGFVec X μ t)) :
    0 ≤ legendreTransform (logMGFVec X μ) x := by
  have h0 := le_legendreTransform (logMGFVec X μ) x 0 hbdd
  simpa [logMGFVec_zero, inner_zero_left] using h0

/-- Pointwise Fenchel–Young for Def's `cramerRateFunction` at integrable directions. -/
theorem le_cramerRateFunction_of_integrable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x t : EuclideanSpace ℝ (Fin d))
    (hbdd : BddAbove (Set.range fun y => ⟪y, x⟫_ℝ - logMGFVec X μ y)) :
    ENNReal.ofReal (⟪t, x⟫_ℝ - logMGFVec X μ t) ≤ cramerRateFunction X μ x := by
  unfold cramerRateFunction
  exact ENNReal.ofReal_le_ofReal (le_legendreTransform _ x t hbdd)

/-- Real Legendre transforms are convex wherever the supporting values stay bounded above. -/
theorem convex_legendreTransform {d : ℕ} (Λ : EuclideanSpace ℝ (Fin d) → ℝ)
    {x y : EuclideanSpace ℝ (Fin d)} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : BddAbove (Set.range fun l => ⟪l, x⟫_ℝ - Λ l))
    (hy : BddAbove (Set.range fun l => ⟪l, y⟫_ℝ - Λ l))
    (hxy : BddAbove (Set.range fun l => ⟪l, a • x + b • y⟫_ℝ - Λ l)) :
    legendreTransform Λ (a • x + b • y) ≤ a * legendreTransform Λ x + b * legendreTransform Λ y := by
  have hterm : ∀ l, ⟪l, a • x + b • y⟫_ℝ - Λ l ≤
      a * (⟪l, x⟫_ℝ - Λ l) + b * (⟪l, y⟫_ℝ - Λ l) := by
    intro l
    have hab' : a * Λ l + b * Λ l = Λ l := by
      calc a * Λ l + b * Λ l = (a + b) * Λ l := by ring
        _ = Λ l := by rw [hab, one_mul]
    simp only [inner_add_right, real_inner_smul_right]
    linarith [hab']
  have hle : ∀ l, ⟪l, a • x + b • y⟫_ℝ - Λ l ≤
      a * legendreTransform Λ x + b * legendreTransform Λ y := by
    intro l
    have hxle := le_legendreTransform Λ x l hx
    have hyle := le_legendreTransform Λ y l hy
    have := hterm l
    nlinarith [mul_le_mul_of_nonneg_left hxle ha, mul_le_mul_of_nonneg_left hyle hb]
  exact ciSup_le hle

/-- Convexity of Def's `cramerRateFunction` under fiberwise bounded-above supporting values. -/
theorem cramerRateFunction_convex {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {x y : EuclideanSpace ℝ (Fin d)} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : BddAbove (Set.range fun t => ⟪t, x⟫_ℝ - logMGFVec X μ t))
    (hy : BddAbove (Set.range fun t => ⟪t, y⟫_ℝ - logMGFVec X μ t))
    (hxy : BddAbove (Set.range fun t => ⟪t, a • x + b • y⟫_ℝ - logMGFVec X μ t)) :
    cramerRateFunction X μ (a • x + b • y) ≤
      ENNReal.ofReal a * cramerRateFunction X μ x +
        ENNReal.ofReal b * cramerRateFunction X μ y := by
  unfold cramerRateFunction
  have hnonx := legendreTransform_logMGFVec_nonneg X μ x hx
  have hnony := legendreTransform_logMGFVec_nonneg X μ y hy
  have hconv := convex_legendreTransform (logMGFVec X μ) ha hb hab hx hy hxy
  have h := ENNReal.ofReal_le_ofReal hconv
  refine h.trans ?_
  have ha0 : 0 ≤ a * legendreTransform (logMGFVec X μ) x := mul_nonneg ha hnonx
  have hb0 : 0 ≤ b * legendreTransform (logMGFVec X μ) y := mul_nonneg hb hnony
  rw [ENNReal.ofReal_add ha0 hb0, ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]


/-- `ofReal` of a real `ciSup` sits below the `iSup` of the `ofReal`s (BddAbove). -/
theorem ofReal_ciSup_le {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hbdd : BddAbove (Set.range f)) :
    ENNReal.ofReal (⨆ i, f i) ≤ ⨆ i, ENNReal.ofReal (f i) := by
  refine le_iSup_iff.mpr fun m hm => ?_
  by_cases hm_top : m = ∞
  · subst hm_top; exact le_top
  · have hle : ∀ i, f i ≤ m.toReal := fun i =>
      (ENNReal.ofReal_le_iff_le_toReal hm_top).mp (hm i)
    -- `ciSup_le` only needs the pointwise bound; `hbdd` documents call-site control.
    have _ := hbdd
    exact (ENNReal.ofReal_le_iff_le_toReal hm_top).mpr (ciSup_le hle)

/-- Global Fenchel–Young: if every dual fiber of the Legendre integrand sits below a rate `J`,
then Def's `cramerRateFunction` sits below `J`. -/
theorem cramerRateFunction_le_of_forall_ofReal_inner_sub_logMGF_le {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : EuclideanSpace ℝ (Fin d)) (J : ENNReal)
    (hbdd : BddAbove (Set.range fun t => ⟪t, x⟫_ℝ - logMGFVec X μ t))
    (h : ∀ t, ENNReal.ofReal (⟪t, x⟫_ℝ - logMGFVec X μ t) ≤ J) :
    cramerRateFunction X μ x ≤ J := by
  unfold cramerRateFunction legendreTransform
  refine (ofReal_ciSup_le (fun t => ⟪t, x⟫_ℝ - logMGFVec X μ t) hbdd).trans ?_
  exact iSup_le h
