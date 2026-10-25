/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part6
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part10
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


section DependentBlocks

variable {D : E → Type*} [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
  [∀ e, Fintype (S e)]

theorem liftDependentPiCylinder_agreeOn
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (K : Set E) (omega : StatMech.ConfigSpace (Sigma D)) (x : ∀ e, S e) :
    agreeOn (dependentWholeBlocks (D := D) K) omega
      (liftDependentPiCylinder decode hdecode K omega x) := by
  intro z hz
  simp only [dependentWholeBlocks, Set.mem_setOf_eq] at hz
  simp [liftDependentPiCylinder, hz]

theorem decodeDependentBlockConfig_lift
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (K : Set E) (omega : StatMech.ConfigSpace (Sigma D)) (x : ∀ e, S e)
    (hx : piAgreeOn K (decodeDependentBlockConfig decode omega) x) :
    decodeDependentBlockConfig decode
      (liftDependentPiCylinder decode hdecode K omega x) = x := by
  funext e
  by_cases he : e ∈ K
  · simpa [decodeDependentBlockConfig, liftDependentPiCylinder, he] using hx e he
  · simpa [decodeDependentBlockConfig, liftDependentPiCylinder, he] using
      congrFun (decodeDependentBlockConfig_encode decode hdecode x) e

theorem piAgreeOn_decodeDependent_of_agreeOn
    (decode : ∀ e, (D e → Bool) → S e) (K : Set E)
    {omega eta : StatMech.ConfigSpace (Sigma D)}
    (h : agreeOn (dependentWholeBlocks (D := D) K)
      omega eta) :
    piAgreeOn K (decodeDependentBlockConfig decode omega)
      (decodeDependentBlockConfig decode eta) := by
  intro e he
  apply congrArg (decode e)
  funext d
  exact (h ⟨e, d⟩ he).symm

theorem piCylinderMin_decodeDependentBlockConfig
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f : (∀ e, S e) → ℝ) (K : Set E)
    (omega : StatMech.ConfigSpace (Sigma D)) :
    piCylinderMin f K (decodeDependentBlockConfig decode omega) =
      cylinderMin
        (f ∘ decodeDependentBlockConfig decode)
        (dependentWholeBlocks (D := D) K) omega := by
  classical
  apply le_antisymm
  · apply Finset.le_inf'
    intro eta heta
    exact Finset.inf'_le _ (mem_piAgreementFiber.mpr
      (piAgreeOn_decodeDependent_of_agreeOn decode K
        (mem_agreementFiber.mp heta)))
  · apply Finset.le_inf'
    intro x hx
    let eta := liftDependentPiCylinder decode hdecode K omega x
    have heta : eta ∈ agreementFiber
        (dependentWholeBlocks (D := D) K) omega :=
      mem_agreementFiber.mpr
        (liftDependentPiCylinder_agreeOn decode hdecode K omega x)
    calc
      cylinderMin
          (f ∘ decodeDependentBlockConfig decode)
          (dependentWholeBlocks (D := D) K) omega ≤
          (f ∘ decodeDependentBlockConfig decode) eta :=
        Finset.inf'_le _ heta
      _ = f x := by
        rw [Function.comp_apply,
          decodeDependentBlockConfig_lift decode hdecode K omega x
            (mem_piAgreementFiber.mp hx)]

theorem piFunctionalDisjointMaxAt_decodeDependent_le
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f g : (∀ e, S e) → ℝ)
    (omega eta : StatMech.ConfigSpace (Sigma D)) :
    piFunctionalDisjointMaxAt f g (decodeDependentBlockConfig decode omega)
        (decodeDependentBlockConfig decode eta) ≤
      functionalDisjointMaxAt
        (f ∘ decodeDependentBlockConfig decode)
        (g ∘ decodeDependentBlockConfig decode) omega eta := by
  classical
  unfold piFunctionalDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  rw [piCylinderMin_decodeDependentBlockConfig decode hdecode,
    piCylinderMin_decodeDependentBlockConfig decode hdecode]
  unfold functionalDisjointMaxAt
  have hbit :
      (dependentWholeBlocks (D := D) pair.1,
        dependentWholeBlocks (D := D) pair.2) ∈
        disjointCoordinatePairs (Sigma D) :=
    mem_disjointCoordinatePairs.mpr
      (dependentWholeBlocks_disjoint (D := D)
        (mem_disjointCoordinatePairs.mp hpair))
  exact Finset.le_sup'
    (fun bitPair : Set (Sigma D) × Set (Sigma D) =>
      cylinderMin (f ∘ decodeDependentBlockConfig decode) bitPair.1 omega *
        cylinderMin (g ∘ decodeDependentBlockConfig decode) bitPair.2 eta)
    hbit

theorem piFunctionalDisjointMax_decodeDependent_le
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f g : (∀ e, S e) → ℝ) (omega : StatMech.ConfigSpace (Sigma D)) :
    piFunctionalDisjointMax f g (decodeDependentBlockConfig decode omega) ≤
      functionalDisjointMax
        (f ∘ decodeDependentBlockConfig decode)
        (g ∘ decodeDependentBlockConfig decode) omega :=
  piFunctionalDisjointMaxAt_decodeDependent_le decode hdecode f g omega omega

set_option maxHeartbeats 20000 in
theorem functionalFamilyBKR_dependentBlocks
    (phi : Sigma D → Bool → ℝ)
    (hphi0 : ∀ z b, 0 ≤ phi z b)
    (hphi1 : ∀ z, phi z false + phi z true = 1)
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    productExpectation phi (fun omega =>
        piFunctionalFamilyDisjointMax F G
          (decodeDependentBlockConfig decode omega)) ≤
      productExpectation phi (fun omega =>
          piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega)) *
        productExpectation phi (fun omega =>
          piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) := by
  let fmax : StatMech.ConfigSpace (Sigma D) → ℝ :=
    piFunctionalFamilyMax F ∘ decodeDependentBlockConfig decode
  let gmax : StatMech.ConfigSpace (Sigma D) → ℝ :=
    piFunctionalFamilyMax G ∘ decodeDependentBlockConfig decode
  have hfmax0 : ∀ omega, 0 ≤ fmax omega := fun omega =>
    piFunctionalFamilyMax_nonneg F hF0 _
  have hgmax0 : ∀ omega, 0 ≤ gmax omega := fun omega =>
    piFunctionalFamilyMax_nonneg G hG0 _
  have hbkr : productExpectation phi (functionalDisjointMax fmax gmax) ≤
      productExpectation phi fmax * productExpectation phi gmax :=
    functionalBKR_real phi hphi0 hphi1 fmax gmax hfmax0 hgmax0
  calc
    productExpectation phi (fun omega =>
        piFunctionalFamilyDisjointMax F G
          (decodeDependentBlockConfig decode omega)) ≤
        productExpectation phi (functionalDisjointMax fmax gmax) := by
      unfold productExpectation
      apply Finset.sum_le_sum
      intro omega _
      apply mul_le_mul_of_nonneg_left _ (pweight_nonneg hphi0 omega)
      have hfamily := piFunctionalFamilyDisjointMaxAt_le_pi F G hF0 hG0 hF hG
        (decodeDependentBlockConfig decode omega)
        (decodeDependentBlockConfig decode omega)
      have hlift := piFunctionalDisjointMax_decodeDependent_le decode hdecode
        (piFunctionalFamilyMax F) (piFunctionalFamilyMax G) omega
      change piFunctionalDisjointMax
        (piFunctionalFamilyMax F) (piFunctionalFamilyMax G)
          (decodeDependentBlockConfig decode omega) ≤
        functionalDisjointMax fmax gmax omega at hlift
      exact hfamily.trans hlift
    _ ≤ productExpectation phi fmax * productExpectation phi gmax := hbkr
    _ = productExpectation phi (fun omega =>
          piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega)) *
        productExpectation phi (fun omega =>
          piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) := rfl

set_option maxHeartbeats 20000 in
theorem dualFunctionalFamilyBKR_dependentBlocks
    (phi : Sigma D → Bool → ℝ)
    (hphi0 : ∀ z b, 0 ≤ phi z b)
    (hphi1 : ∀ z, phi z false + phi z true = 1)
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    dualProductExpectation phi (fun pair =>
        piFunctionalFamilyDisjointMaxAt F G
          (decodeDependentBlockConfig decode pair.1)
          (decodeDependentBlockConfig decode pair.2)) ≤
      productExpectation phi (fun omega =>
        piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega) *
          piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) := by
  let fmax : StatMech.ConfigSpace (Sigma D) → ℝ :=
    piFunctionalFamilyMax F ∘ decodeDependentBlockConfig decode
  let gmax : StatMech.ConfigSpace (Sigma D) → ℝ :=
    piFunctionalFamilyMax G ∘ decodeDependentBlockConfig decode
  have hfmax0 : ∀ omega, 0 ≤ fmax omega := fun omega =>
    piFunctionalFamilyMax_nonneg F hF0 _
  have hgmax0 : ∀ omega, 0 ≤ gmax omega := fun omega =>
    piFunctionalFamilyMax_nonneg G hG0 _
  have hbkr : dualProductExpectation phi (fun pair =>
        functionalDisjointMaxAt fmax gmax pair.1 pair.2) ≤
      productExpectation phi (fun omega => fmax omega * gmax omega) :=
    dualFunctionalBKR_real phi hphi0 hphi1 fmax gmax hfmax0 hgmax0
  calc
    dualProductExpectation phi (fun pair =>
        piFunctionalFamilyDisjointMaxAt F G
          (decodeDependentBlockConfig decode pair.1)
          (decodeDependentBlockConfig decode pair.2)) ≤
        dualProductExpectation phi (fun pair =>
          functionalDisjointMaxAt fmax gmax pair.1 pair.2) := by
      unfold dualProductExpectation
      apply Finset.sum_le_sum
      intro omega _
      apply Finset.sum_le_sum
      intro eta _
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (pweight_nonneg hphi0 omega) (pweight_nonneg hphi0 eta))
      have hfamily := piFunctionalFamilyDisjointMaxAt_le_pi F G hF0 hG0 hF hG
        (decodeDependentBlockConfig decode omega)
        (decodeDependentBlockConfig decode eta)
      have hlift := piFunctionalDisjointMaxAt_decodeDependent_le decode hdecode
        (piFunctionalFamilyMax F) (piFunctionalFamilyMax G) omega eta
      change piFunctionalDisjointMaxAt
        (piFunctionalFamilyMax F) (piFunctionalFamilyMax G)
          (decodeDependentBlockConfig decode omega)
          (decodeDependentBlockConfig decode eta) ≤
        functionalDisjointMaxAt fmax gmax omega eta at hlift
      exact hfamily.trans hlift
    _ ≤ productExpectation phi (fun omega => fmax omega * gmax omega) := hbkr
    _ = productExpectation phi (fun omega =>
          piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega) *
            piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) := rfl

end DependentBlocks
end StatMech.FrontierA
