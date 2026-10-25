/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Structure.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_wallTerminalProductClassification
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl : Site 2}
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hclassR : RlcTwoChannelFullPhysicalRightArcClassifiedBad
      gamma gamma' omega ur vr)
    (hclassL : RlcTwoChannelFullPhysicalLeftArcClassifiedBad
      gamma gamma' omega ul vl) :
    RlcTwoChannelFullPhysicalWallTerminalProductClassification
      gamma gamma' omega (vr := vr) (vl := vl) qr ql := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases hall : ∀ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma'
    · exact Or.inl hall
    · exact Or.inr
        ((rlc_prefix_not_all_fourTrace_iff_exists_nonWallEdge qr).mp hall)
  · by_cases hall : ∀ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma'
    · exact Or.inl hall
    · exact Or.inr
        ((rlc_prefix_not_all_fourTrace_iff_exists_nonWallEdge ql).mp hall)
  · by_cases hloc :
        RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
            gamma gamma' (rlc_dualReflect ur) ∨
          RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
            gamma gamma' (rlc_dualReflect ur)
    · exact Or.inl hloc
    · exact Or.inr ⟨hloc,
        rlc_rightArcClassifiedBad_of_terminal_not_exclusive hclassR hloc⟩
  · by_cases hloc :
        RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
            gamma gamma' (rlc_dualReflect ul) ∨
          RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
            gamma gamma' (rlc_dualReflect ul)
    · exact Or.inl hloc
    · exact Or.inr ⟨hloc,
        rlc_leftArcClassifiedBad_of_terminal_not_exclusive hclassL hloc⟩
  · intro hallR hallL hlocR hlocL
    exact rlc_twoChannelFullPhysical_twoArcWallTerminalFamilyTable
      hfaith qr ql hxPath hyPath hallR hallL hlocR hlocL


end
end StatMech.Universality
