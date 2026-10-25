/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part6
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E D : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D]
  {S : E → Type*} [∀ e, Fintype (S e)]


theorem functionalBKR_finiteCoordinateBlocks
    (phi : E × D → Bool → ℝ)
    (hphi0 : ∀ z b, 0 ≤ phi z b)
    (hphi1 : ∀ z, phi z false + phi z true = 1)
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f g : (∀ e, S e) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    blockProductExpectation phi decode (piFunctionalDisjointMax f g) ≤
      blockProductExpectation phi decode f * blockProductExpectation phi decode g := by
  unfold blockProductExpectation
  calc
    productExpectation phi (piFunctionalDisjointMax f g ∘ decodeBlockConfig decode) ≤
        productExpectation phi
          (functionalDisjointMax (f ∘ decodeBlockConfig decode)
            (g ∘ decodeBlockConfig decode)) := by
      unfold productExpectation
      apply Finset.sum_le_sum
      intro omega _
      exact mul_le_mul_of_nonneg_left
        (piFunctionalDisjointMax_decode_le decode hdecode f g omega)
        (pweight_nonneg hphi0 omega)
    _ ≤ productExpectation phi (f ∘ decodeBlockConfig decode) *
          productExpectation phi (g ∘ decodeBlockConfig decode) :=
      functionalBKR_real phi hphi0 hphi1 _ _
        (fun omega => hf0 (decodeBlockConfig decode omega))
        (fun omega => hg0 (decodeBlockConfig decode omega))


theorem dualFunctionalBKR_finiteCoordinateBlocks
    (phi : E × D → Bool → ℝ)
    (hphi0 : ∀ z b, 0 ≤ phi z b)
    (hphi1 : ∀ z, phi z false + phi z true = 1)
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f g : (∀ e, S e) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    dualProductExpectation phi (fun pair =>
        piFunctionalDisjointMaxAt f g (decodeBlockConfig decode pair.1)
          (decodeBlockConfig decode pair.2)) ≤
      blockProductExpectation phi decode (fun x => f x * g x) := by
  unfold blockProductExpectation
  calc
    dualProductExpectation phi (fun pair =>
        piFunctionalDisjointMaxAt f g (decodeBlockConfig decode pair.1)
          (decodeBlockConfig decode pair.2)) ≤
        dualProductExpectation phi (fun pair =>
          functionalDisjointMaxAt (f ∘ decodeBlockConfig decode)
            (g ∘ decodeBlockConfig decode) pair.1 pair.2) := by
      unfold dualProductExpectation
      apply Finset.sum_le_sum
      intro omega _
      apply Finset.sum_le_sum
      intro eta _
      exact mul_le_mul_of_nonneg_left
        (piFunctionalDisjointMaxAt_decode_le decode hdecode f g omega eta)
        (mul_nonneg (pweight_nonneg hphi0 omega) (pweight_nonneg hphi0 eta))
    _ ≤ productExpectation phi
          ((fun x => f x * g x) ∘ decodeBlockConfig decode) := by
      exact dualFunctionalBKR_real phi hphi0 hphi1 _ _
        (fun omega => hf0 (decodeBlockConfig decode omega))
        (fun omega => hg0 (decodeBlockConfig decode omega))

end StatMech.FrontierA
