/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCompletedHighestCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.HexCorrectedSideDepth
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedShiftedDivergence
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExteriorPeriod.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedCompletedHighestCut.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hexCSCompletedAsymmetricCut
    (T : ℕ) (hT : 1 ≤ T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    HexAsymmetricHighestCut (hexChiE⁻¹ ^ 5) where
  D := {ts : List ℤ // HexCSNewSideWalk T hT ts}
  B₁ := HexCSCompletedTopWalk T hT
  B₂ := HexCSCompletedTopWalk T hT
  wtγ := fun d => hexEndpointSAWwt hexAWStart 1 hexChiE d.1
  wtB₁ := fun b => hexEndpointSAWwt hexAWStart 1 hexChiE b.1
  wtB₂ := fun b => hexEndpointSAWwt hexAWStart 1 hexChiE b.1
  wtγ_nn := fun d => hexEndpointSAWwt_nonneg hexAWStart 1 hexChiE_pos.le d.1
  wtB₁_nn := fun b => hexEndpointSAWwt_nonneg hexAWStart 1 hexChiE_pos.le b.1
  wtB₂_nn := fun b => hexEndpointSAWwt_nonneg hexAWStart 1 hexChiE_pos.le b.1
  split := hexCSCompletedSplit T hT
  split_injective := hexCSCompletedSplit_injective T hT
  weight_bound := by
    intro d
    have hd : (ofTurns hexAWStart 1 d.1).EndpointIsLegalSAW :=
      d.2.1.choose_spec.1
    have hb₁ :
        (ofTurns hexAWStart 1 (hexCSCompletedSplit T hT d).1.1).EndpointIsLegalSAW :=
      (hexCSCompletedSplit T hT d).1.2.choose_spec.1
    have hb₂ :
        (ofTurns hexAWStart 1 (hexCSCompletedSplit T hT d).2.1).EndpointIsLegalSAW :=
      (hexCSCompletedSplit T hT d).2.2.choose_spec.1
    simp only [hexEndpointSAWwt, if_pos hd, if_pos hb₁, if_pos hb₂]
    apply le_of_eq
    rw [← pow_add, hexCSCompletedSplit_length T hT d]
    simp only [endpointNumVertices]
    rw [pow_add]
    field_simp [ne_of_gt hexChiE_pos]
  D_summable := hwalk.comp_injective Subtype.val_injective
  B₁_summable := hwalk.comp_injective Subtype.val_injective
  B₂_summable := hwalk.comp_injective Subtype.val_injective


end
end StatMech.Universality
