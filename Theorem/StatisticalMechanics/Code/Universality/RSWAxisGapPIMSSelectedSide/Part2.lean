/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraph.Part4
import Def.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSSelectedSide.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_axisGapPIMSSourceOpenCase_of_maskedDual_open {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (Site 2))
    (hopen : rlc_dualReflectConfig
      (rlc_maskConfig (rlc_axisGapEdges G)
        (rlc_axisGapAmbientConfig G tau)) e = true) :
    RlcAxisGapPIMSSourceOpenCase G tau e := by
  rw [rlc_maskConfig_axisGapAmbientConfig,
    rlc_dualReflectConfig_eq_pims] at hopen
  by_cases hsource : rlc_pimsEdgeEquiv e ∈ rlc_axisGapEdges G
  · left
    refine ⟨hsource, ?_⟩
    simpa [rlc_axisGapAmbientConfig, hsource] using hopen
  · exact Or.inr hsource


theorem rlc_axisGapPIMSReflectedConfig_open_of_sourceOpenCase {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (Site 2)) (htarget : e ∈ rlc_axisGapEdges G)
    (hcase : RlcAxisGapPIMSSourceOpenCase G tau e) :
    rlc_axisGapPIMSReflectedConfig G tau
      (rlc_axisGapEdgeLift G e htarget) = true := by
  rw [rlc_axisGapPIMSReflectedConfig_apply,
    rlc_axisGapEdgeLift_map]
  rcases hcase with ⟨hsource, hclosed⟩ | hsource
  · rw [rlc_axisGapAmbientConfig_supportEdge G tau hsource, hclosed]
    rfl
  · simp [rlc_axisGapAmbientConfig, hsource]


theorem rlc_axisGapPIMSReflectedConfig_open_of_finite_sourceOpenCase
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (hcase : RlcAxisGapPIMSSourceOpenCase G tau (e.map Subtype.val)) :
    rlc_axisGapPIMSReflectedConfig G tau e = true := by
  rw [rlc_axisGapPIMSReflectedConfig_apply]
  rcases hcase with ⟨hsource, hclosed⟩ | hsource
  · rw [rlc_axisGapAmbientConfig_supportEdge G tau hsource, hclosed]
    rfl
  · simp [rlc_axisGapAmbientConfig, hsource]


end
end StatMech.Universality
