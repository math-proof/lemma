/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Mathlib.MeasureTheory.Function.EssSup
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKREssInfFinite
open MeasureTheory
open scoped BigOperators ENNReal NNReal


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [DecidableEq E] in
theorem agreementFiberMeasure_singleton_ne_zero
    (p : E → ℝ≥0) (hp0 : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (K : Set E) (omega : ConfigSpace E)
    (eta : AgreementFiberPoint K omega) :
    agreementFiberMeasure p (fun e => (hp1 e).le) K omega {eta} ≠ 0 := by
  rw [agreementFiberMeasure, Measure.comap_apply Subtype.val
    Subtype.val_injective (fun _ _ => MeasurableSet.of_discrete)
    _ (measurableSet_singleton eta)]
  have himage : Subtype.val '' ({eta} : Set (AgreementFiberPoint K omega)) =
      {eta.1} := by
    ext z
    simp
  rw [himage, Measure.restrict_apply (measurableSet_singleton eta.1)]
  have hinter : ({eta.1} : Set (ConfigSpace E)) ∩
      {z | agreeOn K omega z} = {eta.1} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.1
    · intro h
      subst z
      exact ⟨rfl, eta.2⟩
  rw [hinter, inhomBernoulliProductMeasure.apply_singleton]
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  cases h : eta.1 e
  · rw [bernoulliMeasure_apply_false]
    exact ENNReal.coe_ne_zero.mpr
      (ne_of_gt (tsub_pos_iff_lt.mpr (hp1 e)))
  · rw [bernoulliMeasure_apply_true]
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (hp0 e))


end StatMech.FrontierA
