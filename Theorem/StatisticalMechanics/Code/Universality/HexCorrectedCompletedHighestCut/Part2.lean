module
public import Def.StatisticalMechanics.Code.Universality.HexCorrectedSideDepth
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedShiftedDivergence
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExteriorPeriod.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part8
public import Def.StatisticalMechanics.Code.Universality.HexCorrectedCompletedHighestCut.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCompletedHighestCut.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hexCSCompletedTop_tsum_eq_mass
    (T : ℕ) (hT : 1 ≤ T) :
    (∑' b : HexCSCompletedTopWalk T hT,
        hexEndpointSAWwt hexAWStart 1 hexChiE b.1) =
      hexCSInfiniteTopMassAtWidth (T + 2) := by
  rw [show hexCSInfiniteTopMassAtWidth (T + 2) =
      hexCSPredicateMass
        (HexCSTopWalkAtWidth (T + 2) (by omega)) by
    simp [hexCSInfiniteTopMassAtWidth],
    hexCSPredicateMass_eq_tsum_subtype]
  apply tsum_congr
  intro b
  have hlegal : (ofTurns hexAWStart 1 b.1).EndpointIsLegalSAW :=
    b.2.choose_spec.1
  simp [hexEndpointSAWwt, hlegal]


end
end StatMech.Universality
