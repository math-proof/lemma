/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedCriticalDivergence


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hexCSPredicateMass_sdiff
    (P Q : List ℤ → Prop)
    (hPQ : ∀ ts, P ts → Q ts)
    (hlegalQ : ∀ ts, Q ts →
      (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    hexCSPredicateMass Q = hexCSPredicateMass P +
      hexCSPredicateMass (fun ts => Q ts ∧ ¬ P ts) := by
  classical
  have hP := hexCSPredicateWeight_summable P
    (fun ts hts => hlegalQ ts (hPQ ts hts)) hwalk
  have hD := hexCSPredicateWeight_summable (fun ts => Q ts ∧ ¬ P ts)
    (fun ts hts => hlegalQ ts hts.1) hwalk
  unfold hexCSPredicateMass
  rw [← hP.tsum_add hD]
  apply tsum_congr
  intro ts
  unfold hexCSPredicateWeight
  by_cases hp : P ts
  · have hq := hPQ ts hp
    simp [hp, hq]
  · by_cases hq : Q ts
    · simp [hp, hq]
    · simp [hp, hq]


end
end StatMech.Universality
