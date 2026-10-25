/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedCriticalDivergence
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

namespace HexCSHighestCut

variable {T : ℕ} {hT : 1 ≤ T}


noncomputable def toHighestCut (H : HexCSHighestCut T hT)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    HexHighestCut hexChiE⁻¹ where
  D := {ts : List ℤ // HexCSNewSideWalk T hT ts}
  B := HexCSNextTopWalk T hT
  wtγ := fun d => hexEndpointSAWwt hexAWStart 1 hexChiE d.1
  wtB := fun b => hexEndpointSAWwt hexAWStart 1 hexChiE b.1
  wtγ_nn := fun d => hexEndpointSAWwt_nonneg hexAWStart 1 hexChiE_pos.le d.1
  wtB_nn := fun b => hexEndpointSAWwt_nonneg hexAWStart 1 hexChiE_pos.le b.1
  split := H.split
  split_inj := H.split_injective
  weight_bound := by
    intro d
    have hd : (ofTurns hexAWStart 1 d.1).EndpointIsLegalSAW :=
      d.2.1.choose_spec.1
    have hb1 : (ofTurns hexAWStart 1 (H.split d).1.1).EndpointIsLegalSAW :=
      (H.split d).1.2.choose_spec.1
    have hb2 : (ofTurns hexAWStart 1 (H.split d).2.1).EndpointIsLegalSAW :=
      (H.split d).2.2.choose_spec.1
    simp only [hexEndpointSAWwt, if_pos hd, if_pos hb1, if_pos hb2]
    apply le_of_eq
    rw [← pow_add, H.length_add_one d, pow_succ]
    field_simp [ne_of_gt hexChiE_pos]
  D_summable := hwalk.comp_injective Subtype.val_injective
  B_summable := hwalk.comp_injective Subtype.val_injective


end HexCSHighestCut
end
end StatMech.Universality
