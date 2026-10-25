/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part5
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E D : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D]
  {S : E → Type*} [∀ e, Fintype (S e)]


theorem liftPiCylinder_agreeOn
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (K : Set E) (omega : ConfigSpace (E × D)) (x : ∀ e, S e) :
    agreeOn (wholeBlocks (D := D) K) omega
      (liftPiCylinder decode hdecode K omega x) := by
  intro z hz
  simp only [wholeBlocks, Set.mem_setOf_eq] at hz
  simp [liftPiCylinder, hz]

theorem decodeBlockConfig_liftPiCylinder
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (K : Set E) (omega : ConfigSpace (E × D)) (x : ∀ e, S e)
    (hx : piAgreeOn K (decodeBlockConfig decode omega) x) :
    decodeBlockConfig decode (liftPiCylinder decode hdecode K omega x) = x := by
  funext e
  by_cases he : e ∈ K
  · simpa [decodeBlockConfig, liftPiCylinder, he] using hx e he
  · simpa [decodeBlockConfig, liftPiCylinder, he] using
      congrFun (decodeBlockConfig_encodeBlockConfig decode hdecode x) e

theorem piAgreeOn_decode_of_agreeOn_wholeBlocks
    (decode : ∀ e, (D → Bool) → S e) (K : Set E)
    {omega eta : ConfigSpace (E × D)}
    (h : agreeOn (wholeBlocks (D := D) K) omega eta) :
    piAgreeOn K (decodeBlockConfig decode omega) (decodeBlockConfig decode eta) := by
  intro e he
  apply congrArg (decode e)
  funext d
  exact (h (e, d) he).symm


theorem piCylinderMin_decodeBlockConfig
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f : (∀ e, S e) → ℝ) (K : Set E) (omega : ConfigSpace (E × D)) :
    piCylinderMin f K (decodeBlockConfig decode omega) =
      cylinderMin (f ∘ decodeBlockConfig decode) (wholeBlocks (D := D) K) omega := by
  classical
  apply le_antisymm
  · apply Finset.le_inf'
    intro eta heta
    exact Finset.inf'_le _ (mem_piAgreementFiber.mpr
      (piAgreeOn_decode_of_agreeOn_wholeBlocks decode K
        (mem_agreementFiber.mp heta)))
  · apply Finset.le_inf'
    intro x hx
    let eta := liftPiCylinder decode hdecode K omega x
    have heta : eta ∈ agreementFiber (wholeBlocks (D := D) K) omega :=
      mem_agreementFiber.mpr (liftPiCylinder_agreeOn decode hdecode K omega x)
    calc
      cylinderMin (f ∘ decodeBlockConfig decode) (wholeBlocks (D := D) K) omega
          ≤ (f ∘ decodeBlockConfig decode) eta := Finset.inf'_le _ heta
      _ = f x := by
        rw [Function.comp_apply, decodeBlockConfig_liftPiCylinder decode hdecode
          K omega x (mem_piAgreementFiber.mp hx)]


theorem piFunctionalDisjointMaxAt_decode_le
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f g : (∀ e, S e) → ℝ) (omega eta : ConfigSpace (E × D)) :
    piFunctionalDisjointMaxAt f g (decodeBlockConfig decode omega)
        (decodeBlockConfig decode eta) ≤
      functionalDisjointMaxAt (f ∘ decodeBlockConfig decode)
        (g ∘ decodeBlockConfig decode) omega eta := by
  classical
  unfold piFunctionalDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  rw [piCylinderMin_decodeBlockConfig decode hdecode,
    piCylinderMin_decodeBlockConfig decode hdecode]
  unfold functionalDisjointMaxAt
  have hbit : (wholeBlocks (D := D) pair.1, wholeBlocks (D := D) pair.2) ∈
      disjointCoordinatePairs (E × D) :=
    mem_disjointCoordinatePairs.mpr
      (wholeBlocks_disjoint (D := D) (mem_disjointCoordinatePairs.mp hpair))
  exact Finset.le_sup'
    (fun bitPair : Set (E × D) × Set (E × D) =>
      cylinderMin (f ∘ decodeBlockConfig decode) bitPair.1 omega *
        cylinderMin (g ∘ decodeBlockConfig decode) bitPair.2 eta)
    hbit

theorem piFunctionalDisjointMax_decode_le
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f g : (∀ e, S e) → ℝ) (omega : ConfigSpace (E × D)) :
    piFunctionalDisjointMax f g (decodeBlockConfig decode omega) ≤
      functionalDisjointMax (f ∘ decodeBlockConfig decode)
        (g ∘ decodeBlockConfig decode) omega :=
  piFunctionalDisjointMaxAt_decode_le decode hdecode f g omega omega


end StatMech.FrontierA
