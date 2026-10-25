/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part9
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorusDirichlet_reflectField
    (i : Fin d) (u : IsingDyadicTorus d k → Real) :
    isingTorusDirichlet (isingTorusReflectField i u) =
      isingTorusDirichlet u := by
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  calc
    (∑ x : IsingDyadicTorus d k, ∑ j : Fin d,
        (isingTorusReflectField i u x -
          isingTorusReflectField i u (x + isingTorusStep j)) *
        (isingTorusReflectField i u x -
          isingTorusReflectField i u (x + isingTorusStep j))) =
      ∑ j : Fin d, ∑ x : IsingDyadicTorus d k,
        (isingTorusReflectField i u x -
          isingTorusReflectField i u (x + isingTorusStep j)) *
        (isingTorusReflectField i u x -
          isingTorusReflectField i u (x + isingTorusStep j)) :=
        Finset.sum_comm
    _ = ∑ j : Fin d, ∑ x : IsingDyadicTorus d k,
        (u x - u (x + isingTorusStep j)) *
          (u x - u (x + isingTorusStep j)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        let e : IsingDyadicTorus d k → IsingDyadicTorus d k := fun x =>
          isingTorusReflectSite i x - isingTorusStep i
        have hinv : Function.Involutive
            (isingTorusReflectSite (k := k) i) :=
          fun x => isingTorusReflectSite_involutive i x
        have hrefl : Function.Bijective
            (isingTorusReflectSite (k := k) i) :=
          hinv.bijective
        have he : Function.Bijective e :=
          (Equiv.subRight (isingTorusStep (k := k) i)).bijective.comp hrefl
        calc
          (∑ x,
              (isingTorusReflectField i u x -
                isingTorusReflectField i u (x + isingTorusStep i)) *
              (isingTorusReflectField i u x -
                isingTorusReflectField i u (x + isingTorusStep i))) =
            ∑ x, (u (e x + isingTorusStep i) - u (e x)) *
              (u (e x + isingTorusStep i) - u (e x)) := by
                apply Finset.sum_congr rfl
                intro x _
                dsimp only [e, isingTorusReflectField]
                rw [isingTorusReflectSite_add_step_same]
                ring
          _ = ∑ x, (u (x + isingTorusStep i) - u x) *
              (u (x + isingTorusStep i) - u x) :=
            he.sum_comp (fun y : IsingDyadicTorus d k =>
              (u (y + isingTorusStep i) - u y) *
                (u (y + isingTorusStep i) - u y))
          _ = ∑ x, (u x - u (x + isingTorusStep i)) *
              (u x - u (x + isingTorusStep i)) := by
                apply Finset.sum_congr rfl
                intro x _
                ring
      · have hinv : Function.Involutive
            (isingTorusReflectSite (k := k) i) :=
          fun x => isingTorusReflectSite_involutive i x
        have hrefl : Function.Bijective
            (isingTorusReflectSite (k := k) i) :=
          hinv.bijective
        calc
          (∑ x,
              (isingTorusReflectField i u x -
                isingTorusReflectField i u (x + isingTorusStep j)) *
              (isingTorusReflectField i u x -
                isingTorusReflectField i u (x + isingTorusStep j))) =
            ∑ x, (u (isingTorusReflectSite i x) -
              u (isingTorusReflectSite i x + isingTorusStep j)) *
              (u (isingTorusReflectSite i x) -
              u (isingTorusReflectSite i x + isingTorusStep j)) := by
                apply Finset.sum_congr rfl
                intro x _
                dsimp only [isingTorusReflectField]
                rw [isingTorusReflectSite_add_step_of_ne i j hji]
          _ = ∑ x, (u x - u (x + isingTorusStep j)) *
              (u x - u (x + isingTorusStep j)) :=
            hrefl.sum_comp (fun y : IsingDyadicTorus d k =>
              (u y - u (y + isingTorusStep j)) *
                (u y - u (y + isingTorusStep j)))
    _ = ∑ x : IsingDyadicTorus d k, ∑ j : Fin d,
        (u x - u (x + isingTorusStep j)) *
          (u x - u (x + isingTorusStep j)) := Finset.sum_comm

theorem isingTorusReflectField_add
    (i : Fin d) (u v : IsingDyadicTorus d k → Real) :
    isingTorusReflectField i (u + v) =
      isingTorusReflectField i u + isingTorusReflectField i v := by
  rfl

theorem isingTorusDirichletBilinear_reflectField
    (i : Fin d) (u v : IsingDyadicTorus d k → Real) :
    isingTorusDirichletBilinear
        (isingTorusReflectField i u) (isingTorusReflectField i v) =
      isingTorusDirichletBilinear u v := by
  have hadd := isingTorusDirichlet_add u v
  have haddR := isingTorusDirichlet_add
    (isingTorusReflectField i u) (isingTorusReflectField i v)
  rw [← isingTorusReflectField_add,
    isingTorusDirichlet_reflectField,
    isingTorusDirichlet_reflectField,
    isingTorusDirichlet_reflectField] at haddR
  linarith

theorem isingTorusEmbedUpper_eq_reflect_embedLower
    (i : Fin d) (u : IsingTorusLowerSite (k := k) i → Real) :
    isingTorusEmbedUpper i u =
      isingTorusReflectField i (isingTorusEmbedLower i u) := by
  funext x
  by_cases hx : isingTorusInLowerHalf i x
  · have hr : ¬ isingTorusInLowerHalf i (isingTorusReflectSite i x) :=
      fun hr => (isingTorusReflectSite_not_lower_iff i x).mp hr hx
    simp [isingTorusEmbedUpper, isingTorusReflectField,
      isingTorusEmbedLower, hx, hr]
  · have hr : isingTorusInLowerHalf i (isingTorusReflectSite i x) :=
      (isingTorusReflectSite_not_lower_iff i x).mpr hx
    simp [isingTorusEmbedUpper, isingTorusReflectField,
      isingTorusEmbedLower, hx, hr]

theorem isingTorusUpperHalfWeight_eq_lowerHalfWeight
    (i : Fin d) (beta : Real)
    (u : IsingTorusLowerSite (k := k) i → Real) :
    isingTorusUpperHalfWeight i beta u =
      isingTorusLowerHalfWeight i beta u := by
  unfold isingTorusUpperHalfWeight isingTorusLowerHalfWeight
  rw [isingTorusEmbedUpper_eq_reflect_embedLower,
    isingTorusDirichlet_reflectField]

theorem isingTorus_upperFeatureDot_eq_lowerFeatureDot
    (i : Fin d)
    (u v : IsingTorusLowerSite (k := k) i → Real) :
    (∑ e : IsingTorusDirectedEdge d k,
        isingTorusUpperGradientFeature i u e *
          isingTorusUpperGradientFeature i v e) =
      ∑ e : IsingTorusDirectedEdge d k,
        isingTorusLowerGradientFeature i u e *
          isingTorusLowerGradientFeature i v e := by
  have href := isingTorusDirichletBilinear_reflectField i
    (isingTorusEmbedLower i u) (isingTorusEmbedLower i v)
  rw [← isingTorusEmbedUpper_eq_reflect_embedLower,
    ← isingTorusEmbedUpper_eq_reflect_embedLower] at href
  unfold isingTorusUpperGradientFeature isingTorusLowerGradientFeature
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [neg_mul_neg]
  exact href


theorem isingTorusShiftedPartition_eq_halves
    (i : Fin d) (beta : Real) (h : IsingDyadicTorus d k → Real) :
    isingTorusShiftedPartition beta h =
      ∑ lower : ConfigSpace (IsingTorusLowerSite (k := k) i),
        ∑ upper : ConfigSpace (IsingTorusLowerSite (k := k) i),
          isingTorusLowerHalfWeight i beta
              (isingTorusLowerValues i h lower) *
            isingTorusUpperHalfWeight i beta
              (isingTorusUpperValues i h upper) *
            Real.exp (beta *
              ∑ e : IsingTorusDirectedEdge d k,
                isingTorusBoundaryFeature i
                    (isingTorusLowerValues i h lower) e *
                  isingTorusBoundaryFeature i
                    (isingTorusUpperValues i h upper) e) := by
  unfold isingTorusShiftedPartition
  rw [← (isingTorusHalvesEquiv (k := k) i).bijective.sum_comp
    (fun sigma : ConfigSpace (IsingDyadicTorus d k) =>
      Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma + h))),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro lower _
  apply Finset.sum_congr rfl
  intro upper _
  change Real.exp (-(beta / 2) * isingTorusDirichlet
      (isingTorusSpinField (isingTorusGlueHalves i lower upper) + h)) = _
  rw [isingTorusSpinGlue_add_field_eq_embeds,
    isingTorus_shiftedWeight_factor_boundary]

theorem isingTorusLowerValues_polarizeLower
    (i : Fin d) (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusLowerValues i (isingTorusPolarizeLower i h) sigma =
      isingTorusLowerValues i h sigma := by
  funext x
  simp [isingTorusLowerValues, isingTorusPolarizeLower, x.2]

theorem isingTorusUpperValues_polarizeLower
    (i : Fin d) (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusUpperValues i (isingTorusPolarizeLower i h) sigma =
      isingTorusLowerValues i h sigma := by
  funext x
  have hr : ¬ isingTorusInLowerHalf i (isingTorusReflectSite i x.1) :=
    fun hr => (isingTorusReflectSite_not_lower_iff i x.1).mp hr x.2
  simp [isingTorusUpperValues, isingTorusLowerValues,
    isingTorusPolarizeLower, hr]

theorem isingTorusLowerValues_polarizeUpper
    (i : Fin d) (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusLowerValues i (isingTorusPolarizeUpper i h) sigma =
      isingTorusUpperValues i h sigma := by
  funext x
  simp [isingTorusLowerValues, isingTorusUpperValues,
    isingTorusPolarizeUpper, x.2]

theorem isingTorusUpperValues_polarizeUpper
    (i : Fin d) (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusUpperValues i (isingTorusPolarizeUpper i h) sigma =
      isingTorusUpperValues i h sigma := by
  funext x
  have hr : ¬ isingTorusInLowerHalf i (isingTorusReflectSite i x.1) :=
    fun hr => (isingTorusReflectSite_not_lower_iff i x.1).mp hr x.2
  simp [isingTorusUpperValues, isingTorusPolarizeUpper, hr]


theorem isingTorusShiftedPartition_polarization
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (h : IsingDyadicTorus d k → Real) :
    2 * isingTorusShiftedPartition beta h ≤
      isingTorusShiftedPartition beta (isingTorusPolarizeLower i h) +
        isingTorusShiftedPartition beta (isingTorusPolarizeUpper i h) := by
  rw [isingTorusShiftedPartition_eq_halves i beta h,
    isingTorusShiftedPartition_eq_halves i beta
      (isingTorusPolarizeLower i h),
    isingTorusShiftedPartition_eq_halves i beta
      (isingTorusPolarizeUpper i h)]
  simp_rw [isingTorusLowerValues_polarizeLower,
    isingTorusUpperValues_polarizeLower,
    isingTorusLowerValues_polarizeUpper,
    isingTorusUpperValues_polarizeUpper,
    isingTorusUpperHalfWeight_eq_lowerHalfWeight]
  exact exp_dotProduct_two_family_reflection_inequality beta hbeta
    (fun sigma e => isingTorusBoundaryFeature i
      (isingTorusLowerValues i h sigma) e)
    (fun sigma e => isingTorusBoundaryFeature i
      (isingTorusUpperValues i h sigma) e)
    (fun sigma => isingTorusLowerHalfWeight i beta
      (isingTorusLowerValues i h sigma))
    (fun sigma => isingTorusLowerHalfWeight i beta
      (isingTorusUpperValues i h sigma))

end StatMech.FrontierA
