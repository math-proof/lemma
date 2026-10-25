/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripMassLimits.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCriticalDivergence.Part3
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripColumns.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hexCSPredicateMass_eq_tsum_subtype (P : List ℤ → Prop) :
    hexCSPredicateMass P =
      ∑' w : {ts : List ℤ // P ts},
        hexChiE ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices := by
  symm
  calc
    (∑' w : {ts : List ℤ // P ts},
        hexChiE ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices) =
        ∑' ts : List ℤ, (setOf P).indicator
          (fun us => hexChiE ^
            (ofTurns hexAWStart 1 us).endpointNumVertices) ts :=
      tsum_subtype (setOf P)
        (fun ts => hexChiE ^ (ofTurns hexAWStart 1 ts).endpointNumVertices)
    _ = hexCSPredicateMass P := by
      unfold hexCSPredicateMass
      apply tsum_congr
      intro ts
      classical
      simp [hexCSPredicateWeight, Set.indicator]


theorem hecd_correctedTop_columnSum
    (T : ℕ) (hT : 0 < T) :
    hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth
        hexCSTopWalkWidth T =
      hexCSPredicateMass (HexCSTopWalkAtWidth T hT) := by
  rw [hexCSPredicateMass_eq_tsum_subtype]
  unfold hecd_columnSum HexColumnEmb.fiberSum
  change (∑' i : {w : {ts : List ℤ // HexCSTopWalkAnyWidth ts} //
      hexCSTopWalkWidth w = T},
      hexEndpointSAWwt hexAWStart 1 hexChiE i.1.1) =
    ∑' w : {ts : List ℤ // HexCSTopWalkAtWidth T hT ts},
      hexChiE ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices
  rw [← (hexCSTopFiberEquiv T hT).tsum_eq
    (fun w => hexEndpointSAWwt hexAWStart 1 hexChiE w.1.1)]
  apply tsum_congr
  intro w
  have hlegal : (ofTurns hexAWStart 1 w.1).EndpointIsLegalSAW :=
    w.2.choose_spec.1
  change hexEndpointSAWwt hexAWStart 1 hexChiE w.1 =
    hexChiE ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices
  simp [hexEndpointSAWwt, hlegal]

theorem hecd_correctedTop_columnSum_summable
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    Summable (hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth
      hexCSTopWalkWidth) :=
  hecd_columnSum_summable hexAWStart 1 HexCSTopWalkAnyWidth
    hexCSTopWalkWidth hwalk

end
end StatMech.Universality
