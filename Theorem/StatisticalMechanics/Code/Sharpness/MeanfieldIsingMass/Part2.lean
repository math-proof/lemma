/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.WeightedFieldGhost.Part2
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part2
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open FluxEdgeCopy

open FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem sum_baseCutMass_eq_one_sub_mag_sq (beta h : ℝ) (o : V) :
    (∑ T : Finset V, if o ∈ T then
      isingCutMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
      else 0) =
      1 - (Ising.isingExpectation G beta h (Ising.spinProd {o})) ^ 2 := by
  classical
  have hghost := sum_isingCutMass_eq_one_sub_sq
    (withGhost G) beta (ghostCoupling h beta (fun _ => 1))
    (o := some o) (g := none) (by simp)
  let F : Finset (Option V) → ℝ := fun S =>
    if some o ∈ S then
      isingCutMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) none S
    else 0
  have hrestrict :
      (∑ S : Finset (Option V), F S) =
        ∑ S : Finset (Option V), if none ∉ S then F S else 0 := by
    apply Finset.sum_congr rfl
    intro S _
    by_cases hg : none ∉ S
    · rw [if_pos hg]
    · rw [if_neg hg]
      have hgmem : none ∈ S := not_not.mp hg
      by_cases ho : some o ∈ S
      · simp [F, ho, isingCutMass_eq_zero_of_mem_root
          (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) none S hgmem]
      · simp [F, ho]
  have hsubtype :
      (∑ S : Finset (Option V), if none ∉ S then F S else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro S
    simp
  have hreindex :
      (∑ T : Finset V, if o ∈ T then
        isingCutMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
        else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    apply Fintype.sum_equiv ghostFreeFinsetEquiv
    intro T
    simp only [ghostFreeFinsetEquiv, Equiv.ofBijective_apply]
    change
      (if o ∈ T then
        isingCutMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
      else 0) = F (T.map someEmb)
    by_cases ho : o ∈ T <;> simp [F, ho]
  have hdict := fgd_expectationJ_ghost_eq_odd G beta h ({o} : Finset V) (by simp)
  have hsource : insert none (({o} : Finset V).map someEmb) =
      ({some o, none} : Finset (Option V)) := by
    ext z
    cases z <;> simp [someEmb]
  rw [hsource] at hdict
  change (∑ S : Finset (Option V), F S) = _ at hghost
  rw [hreindex, ← hsubtype, ← hrestrict, hghost, hdict]


theorem sum_localCorr_baseCutMass_eq_fieldCovariance
    (beta h : ℝ) {o x : V} (hox : o ≠ x) :
    (∑ T : Finset V,
      if o ∈ T ∧ x ∈ T then
        expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} *
          isingCutMass (withGhost G) beta
            (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
      else 0) =
      Ising.isingExpectation G beta h (Ising.spinProd {o, x}) -
        Ising.isingExpectation G beta h (Ising.spinProd {o}) *
          Ising.isingExpectation G beta h (Ising.spinProd {x}) := by
  classical
  have hghost := sum_localCorr_mul_fieldGhostCutMass_eq_covariance G beta h hox
  let F : Finset (Option V) → ℝ := fun S =>
    if some o ∈ S ∧ some x ∈ S then
      expectationJ (withGhost G) beta
          (couplingIn (ghostCoupling h beta (fun _ => 1)) S)
          {some o, some x} *
        isingCutMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) none S
    else 0
  have hsplit :
      (∑ S : Finset (Option V),
        if some o ∈ S ∧ some x ∈ S ∧ none ∉ S then
          expectationJ (withGhost G) beta
              (couplingIn (ghostCoupling h beta (fun _ => 1)) S)
              {some o, some x} *
            isingCutMass (withGhost G) beta
              (ghostCoupling h beta (fun _ => 1)) none S
        else 0) =
        ∑ S : Finset (Option V), if none ∉ S then F S else 0 := by
    apply Finset.sum_congr rfl
    intro S _
    by_cases hg : none ∉ S <;>
      by_cases ho : some o ∈ S <;>
      by_cases hx : some x ∈ S <;> simp [F, hg, ho, hx]
  have hsubtype :
      (∑ S : Finset (Option V), if none ∉ S then F S else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro S
    simp
  have hreindex :
      (∑ T : Finset V,
        if o ∈ T ∧ x ∈ T then
          expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} *
            isingCutMass (withGhost G) beta
              (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
        else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    apply Fintype.sum_equiv ghostFreeFinsetEquiv
    intro T
    simp only [ghostFreeFinsetEquiv, Equiv.ofBijective_apply]
    change
      (if o ∈ T ∧ x ∈ T then
        expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} *
          isingCutMass (withGhost G) beta
            (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
      else 0) = F (T.map someEmb)
    by_cases ho : o ∈ T <;> by_cases hx : x ∈ T
    · simp [F, ho, hx, localCorr_fieldGhost_map_some G beta h T hox]
    · simp [F, ho, hx]
    · simp [F, ho, hx]
    · simp [F, ho, hx]
  rw [hreindex, ← hsubtype, ← hsplit]
  exact hghost


theorem normalizedDeltaLowerMass_fieldGhost (beta h : ℝ)
    {o x y : V} (hox : o ≠ x) :
    (currentSum (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      isingDeltaLowerMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none =
      ∑ T : Finset V,
        if o ∈ T ∧ x ∈ T ∧ y ∉ T then
          expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} *
            isingCutMass (withGhost G) beta
              (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
        else 0 := by
  classical
  let Z := currentSum (withGhost G) beta
    (ghostCoupling h beta (fun _ => 1)) ∅
  let F : Finset (Option V) → ℝ := fun S =>
    if some o ∈ S ∧ some x ∈ S ∧ some y ∉ S then
      expectationJ (withGhost G) beta
          (couplingIn (ghostCoupling h beta (fun _ => 1)) S)
          {some o, some x} *
        isingCutMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) none S
    else 0
  have hscaled :
      Z⁻¹ ^ 2 * isingDeltaLowerMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none =
        ∑ S : Finset (Option V), if none ∉ S then F S else 0 := by
    unfold isingDeltaLowerMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hoS : some o ∈ S <;> by_cases hxS : some x ∈ S <;>
      by_cases hyS : some y ∉ S <;> by_cases hgS : none ∉ S <;>
      simp [F, isingCutMass, Z, hoS, hxS, hyS, hgS] <;> ring
  have hsubtype :
      (∑ S : Finset (Option V), if none ∉ S then F S else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro S
    simp
  have hreindex :
      (∑ T : Finset V,
        if o ∈ T ∧ x ∈ T ∧ y ∉ T then
          expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} *
            isingCutMass (withGhost G) beta
              (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
        else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    apply Fintype.sum_equiv ghostFreeFinsetEquiv
    intro T
    simp only [ghostFreeFinsetEquiv, Equiv.ofBijective_apply]
    change
      (if o ∈ T ∧ x ∈ T ∧ y ∉ T then
        expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} *
          isingCutMass (withGhost G) beta
            (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
      else 0) = F (T.map someEmb)
    by_cases ho : o ∈ T <;> by_cases hx : x ∈ T <;> by_cases hy : y ∉ T
    · simp [F, ho, hx, hy, localCorr_fieldGhost_map_some G beta h T hox]
    · simp [F, ho, hx, hy]
    · simp [F, ho, hx, hy]
    · simp [F, ho, hx, hy]
    · simp [F, ho, hx, hy]
    · simp [F, ho, hx, hy]
    · simp [F, ho, hx, hy]
    · simp [F, ho, hx, hy]
  rw [hscaled, hsubtype, ← hreindex]


theorem normalizedDeltaSelfLowerMass_fieldGhost (beta h : ℝ) (o y : V) :
    (currentSum (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      isingDeltaSelfLowerMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) (some o) (some y) none =
      ∑ T : Finset V,
        if o ∈ T ∧ y ∉ T then
          isingCutMass (withGhost G) beta
            (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
        else 0 := by
  classical
  let Z := currentSum (withGhost G) beta
    (ghostCoupling h beta (fun _ => 1)) ∅
  let F : Finset (Option V) → ℝ := fun S =>
    if some o ∈ S ∧ some y ∉ S then
      isingCutMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) none S
    else 0
  have hscaled :
      Z⁻¹ ^ 2 * isingDeltaSelfLowerMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) (some o) (some y) none =
        ∑ S : Finset (Option V), if none ∉ S then F S else 0 := by
    unfold isingDeltaSelfLowerMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hoS : some o ∈ S <;> by_cases hyS : some y ∉ S <;>
      by_cases hgS : none ∉ S <;>
      simp [F, isingCutMass, Z, hoS, hyS, hgS] <;> ring
  have hsubtype :
      (∑ S : Finset (Option V), if none ∉ S then F S else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro S
    simp
  have hreindex :
      (∑ T : Finset V,
        if o ∈ T ∧ y ∉ T then
          isingCutMass (withGhost G) beta
            (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
        else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    apply Fintype.sum_equiv ghostFreeFinsetEquiv
    intro T
    simp only [ghostFreeFinsetEquiv, Equiv.ofBijective_apply]
    change
      (if o ∈ T ∧ y ∉ T then
        isingCutMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
      else 0) = F (T.map someEmb)
    by_cases ho : o ∈ T <;> by_cases hy : y ∉ T <;> simp [F, ho, hy]
  rw [hscaled, hsubtype, ← hreindex]


end Sharpness
end StatMech
