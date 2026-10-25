/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedCriticalDivergence
import Structure.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hexCSInfiniteSideMassAtWidth_sdiff
    (T : ℕ) (hT : 1 ≤ T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    hexCSInfiniteSideMassAtWidth (T + 1) -
        hexCSInfiniteSideMassAtWidth T =
      hexCSPredicateMass (HexCSNewSideWalk T hT) := by
  let P := HexCSSideWalkAtWidth T (by omega)
  let Q := HexCSSideWalkAtWidth (T + 1) (by omega)
  have hPQ : ∀ ts, P ts → Q ts := by
    intro ts hts
    obtain ⟨L, hL⟩ := hts
    exact ⟨L, hexCSSideWalk_mono (Nat.le_succ T) le_rfl hL⟩
  have hsplit := hexCSPredicateMass_sdiff P Q hPQ
    (fun ts hts => hts.choose_spec.1) hwalk
  have hsideT : hexCSInfiniteSideMassAtWidth T =
      hexCSPredicateMass P := by
    simp [hexCSInfiniteSideMassAtWidth, P, show 0 < T by omega]
  have hsideNext : hexCSInfiniteSideMassAtWidth (T + 1) =
      hexCSPredicateMass Q := by
    simp [hexCSInfiniteSideMassAtWidth, Q]
  rw [hsideT, hsideNext]
  change hexCSPredicateMass Q - hexCSPredicateMass P =
    hexCSPredicateMass (fun ts => Q ts ∧ ¬ P ts)
  linarith

theorem hexCSNewSide_tsum_eq_difference
    (T : ℕ) (hT : 1 ≤ T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    (∑' d : {ts : List ℤ // HexCSNewSideWalk T hT ts},
        hexEndpointSAWwt hexAWStart 1 hexChiE d.1) =
      hexCSInfiniteSideMassAtWidth (T + 1) -
        hexCSInfiniteSideMassAtWidth T := by
  rw [hexCSInfiniteSideMassAtWidth_sdiff T hT hwalk,
    hexCSPredicateMass_eq_tsum_subtype]
  apply tsum_congr
  intro d
  have hlegal : (ofTurns hexAWStart 1 d.1).EndpointIsLegalSAW :=
    d.2.1.choose_spec.1
  simp [hexEndpointSAWwt, hlegal]

theorem hexCSNextTop_tsum_eq_mass
    (T : ℕ) (hT : 1 ≤ T) :
    (∑' b : HexCSNextTopWalk T hT,
        hexEndpointSAWwt hexAWStart 1 hexChiE b.1) =
      hexCSInfiniteTopMassAtWidth (T + 1) := by
  rw [show hexCSInfiniteTopMassAtWidth (T + 1) =
      hexCSPredicateMass
        (HexCSTopWalkAtWidth (T + 1) (by omega)) by
    simp [hexCSInfiniteTopMassAtWidth],
    hexCSPredicateMass_eq_tsum_subtype]
  apply tsum_congr
  intro b
  have hlegal : (ofTurns hexAWStart 1 b.1).EndpointIsLegalSAW :=
    b.2.choose_spec.1
  simp [hexEndpointSAWwt, hlegal]

end
end StatMech.Universality
