/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/IsotypicPeterWeyl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
import Lemma.Complex.IsKFinite0
import Def.v1.Atlas.LieGroups.code.KFiniteProps.Part4
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Abbrev.v1.Atlas.LieGroups.code.IsotypicPeterWeyl


noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

section L2K

variable (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsHaarMeasure]

def leftTranslationCM : C(K, C(K, K)) :=
  ContinuousMap.curry ⟨fun p : K × K => p.1⁻¹ * p.2, continuous_fst.inv.mul continuous_snd⟩

open MeasureTheory in
def leftRegularRep : ContinuousRep K (L2 K μ) where
  toMonoidHom := {
    toFun := fun g =>
      (Lp.compMeasurePreservingₗ ℂ (fun x => g⁻¹ * x)
        (measurePreserving_mul_left μ g⁻¹)).mkContinuous 1 (by
        intro f; simp only [one_mul]
        exact le_of_eq (Lp.norm_compMeasurePreserving f (measurePreserving_mul_left μ g⁻¹)))
    map_one' := by
      apply ContinuousLinearMap.ext; intro f
      simp only [LinearMap.mkContinuous_apply, Lp.compMeasurePreservingₗ_apply,
        ContinuousLinearMap.one_apply]
      ext1
      refine (Lp.coeFn_compMeasurePreserving _ _).trans ?_
      filter_upwards with x; simp
    map_mul' := fun g₁ g₂ => by
      apply ContinuousLinearMap.ext; intro f
      simp only [LinearMap.mkContinuous_apply, Lp.compMeasurePreservingₗ_apply,
        ContinuousLinearMap.mul_apply]
      change Lp.compMeasurePreserving _ _ f =
             Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f)
      rw [← Lp.compMeasurePreserving_comp_apply]
      ext1
      refine ((Lp.coeFn_compMeasurePreserving _ _).trans ?_).trans
        (Lp.coeFn_compMeasurePreserving _ _).symm
      filter_upwards with x; simp [mul_assoc]
  }
  continuous_action := by sorry

end L2K
end ContinuousRep
end
