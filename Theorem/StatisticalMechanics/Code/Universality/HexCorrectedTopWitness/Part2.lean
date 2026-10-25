/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedTopWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Def.StatisticalMechanics.Code.Universality.HexCorrectedTopWitness


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hexCSTopWalkAtWidth_one_nonempty :
    ∃ ts, HexCSTopWalkAtWidth 1 (by norm_num) ts := by
  exact ⟨[1, -1], hexCSTopOneData.mem_topAtWidth (by norm_num)⟩


theorem hexCS_critical_divergence_of_recurrence_concrete
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
    (hwindow : ∀ T L (hT : 0 < T), HexCSBoundaryWindowLaw T L hT)
    (hrec : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE) →
      ∀ T, 1 ≤ T →
        hexCSInfiniteSideMassAtWidth (T + 1) -
            hexCSInfiniteSideMassAtWidth T ≤
          hexChiE⁻¹ * (hexCSInfiniteTopMassAtWidth (T + 1)) ^ 2) :
    ¬ Summable
      (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) :=
  hexCS_critical_divergence_of_recurrence hlocal hwindow hrec
    hexCSTopWalkAtWidth_one_nonempty


theorem hexCS_critical_divergence_of_highestCuts
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
    (hwindow : ∀ T L (hT : 0 < T), HexCSBoundaryWindowLaw T L hT)
    (HC : ∀ T (hT : 1 ≤ T), HexCSHighestCut T hT) :
    ¬ Summable
      (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) :=
  hexCS_critical_divergence_of_recurrence_concrete hlocal hwindow
    (hexCS_highestCuts_recurrence HC)

end
end StatMech.Universality
