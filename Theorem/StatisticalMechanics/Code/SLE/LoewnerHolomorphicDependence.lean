/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part15
import Mathlib.Analysis.Complex.Conformal
open Complex Set Metric Filter Topology
open scoped Interval


namespace StatMech.SLE

noncomputable section

theorem linearODE_terminal_eq_initial_mul_exp_integral
    {T : Real} (hT : 0 <= T) {a f : Real -> Complex}
    (ha : ContinuousOn a (Icc (0 : Real) T))
    (hf : ContinuousOn f (Icc (0 : Real) T))
    (hderiv : ∀ t ∈ Icc (0 : Real) T,
      HasDerivWithinAt f (a t * f t) (Icc (0 : Real) T) t) :
    f T = f 0 * Complex.exp (∫ s in (0 : Real)..T, a s) := by
  rcases hT.eq_or_lt with rfl | hTpos
  · simp
  let A : Real -> Complex := fun t => ∫ s in (0 : Real)..t, a s
  let r : Real -> Complex := fun t => Complex.exp (-A t) * f t
  have hA : ∀ t ∈ Icc (0 : Real) T,
      HasDerivWithinAt A (a t) (Icc (0 : Real) T) t := by
    intro t ht
    letI : Fact (t ∈ Icc (0 : Real) T) := ⟨ht⟩
    apply intervalIntegral.integral_hasDerivWithinAt_right
    · apply ContinuousOn.intervalIntegrable
      exact ha.mono (by
        rw [uIcc_of_le ht.1]
        exact Icc_subset_Icc_right ht.2)
    · exact ha.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
    · exact ha t ht
  have hr : ∀ t ∈ Icc (0 : Real) T,
      HasDerivWithinAt r 0 (Icc (0 : Real) T) t := by
    intro t ht
    have hexp : HasDerivWithinAt (fun s => Complex.exp (-A s))
        (Complex.exp (-A t) * (-a t)) (Icc (0 : Real) T) t := by
      simpa only [Function.comp_apply] using
        (Complex.hasDerivAt_exp (-A t)).comp_hasDerivWithinAt t (hA t ht).neg
    dsimp only [r]
    convert hexp.mul (hderiv t ht) using 1
    all_goals ring
  have hrdiff : DifferentiableOn Real r (Icc (0 : Real) T) :=
    fun t ht => (hr t ht).differentiableWithinAt
  have hrfderiv : ∀ t ∈ Icc (0 : Real) T,
      fderivWithin Real r (Icc (0 : Real) T) t = 0 := by
    intro t ht
    simpa using (hr t ht).hasFDerivWithinAt.fderivWithin
      ((uniqueDiffOn_Icc hTpos).uniqueDiffWithinAt ht)
  have hconst : r 0 = r T :=
    (convex_Icc (0 : Real) T).is_const_of_fderivWithin_eq_zero
      hrdiff hrfderiv ⟨le_rfl, hTpos.le⟩ ⟨hTpos.le, le_rfl⟩
  have hconst' : f 0 = Complex.exp (-(∫ s in (0 : Real)..T, a s)) * f T := by
    simpa [r, A] using hconst
  calc
    f T = Complex.exp (∫ s in (0 : Real)..T, a s) *
        (Complex.exp (-(∫ s in (0 : Real)..T, a s)) * f T) := by
      rw [<- mul_assoc, <- Complex.exp_add]
      simp
    _ = Complex.exp (∫ s in (0 : Real)..T, a s) * f 0 := by rw [<- hconst']
    _ = f 0 * Complex.exp (∫ s in (0 : Real)..T, a s) := mul_comm _ _


theorem loewnerField_hasDerivAt_initial
    (W : Real -> Real) (t : Real) {z : Complex}
    (hz : z ≠ (W t : Complex)) :
    HasDerivAt (loewnerField W t)
      (-2 / (z - (W t : Complex)) ^ 2) z := by
  have hden : z - (W t : Complex) ≠ 0 := sub_ne_zero.mpr hz
  simpa [loewnerField, hden] using
    (hasDerivAt_const z (2 : Complex)).div
      ((hasDerivAt_id z).sub_const (W t : Complex)) hden


end
end StatMech.SLE
