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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part28
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_exclusiveReflectedRightEdge_sourceWitness
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {p z : Site 2}
    (hpExclusive :
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' p)
    (hpzAdj : (hypercubicLattice 2).Adj p z)
    (hpzTrace : s(p, z) ∈ rlc_reflectedPathEdges gamma.1) :
    ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      source.1.map Subtype.val = s(p, z) := by
  have hpzFour : s(p, z) ∈
      rlc_connectorFourTraceEdges gamma gamma' := by
    rw [rlc_connectorFourTraceEdges]
    apply Finset.mem_union_right
    rw [rlc_connectorReflectedTraceEdges]
    exact Finset.mem_union_left _ hpzTrace
  have hpBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
    gamma gamma' hpzFour (Sym2.mem_mk_left _ _)
  have hzBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
    gamma gamma' hpzFour (Sym2.mem_mk_right _ _)
  have hpBox : p ∈ rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using
      (rlc_connectorBarrier_mem_connectorBox gamma gamma' hpBarrier)
  have hzBox : z ∈ rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using
      (rlc_connectorBarrier_mem_connectorBox gamma gamma' hzBarrier)
  let ps : RlcConnectorVertex n := ⟨p, hpBox⟩
  let zs : RlcConnectorVertex n := ⟨z, hzBox⟩
  have hreflected : (rlc_connectorReflectedTraceWiring
      gamma gamma').Adj ps zs := by
    refine ⟨hpzAdj, ?_⟩
    rw [rlc_connectorReflectedTraceEdges, Finset.mem_union]
    exact Or.inl (by simpa [ps, zs] using hpzTrace)
  have horiginal : ¬(rlc_connectorTraceWiring gamma gamma').Adj ps zs := by
    rintro ⟨_hAdj, htrace⟩
    rw [Finset.mem_union] at htrace
    rcases htrace with hright | hleft
    · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
      exact hpExclusive.2.2.1 (by simpa [ps] using hends.1)
    · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
      exact hpExclusive.2.2.2 (by simpa [ps] using hends.1)
  have htwo : (rlc_connectorTwoChannelGraph gamma gamma').Adj ps zs :=
    ⟨Or.inr hreflected, horiginal⟩
  let source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
    ⟨s(ps, zs), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
  exact ⟨source, by simp [source, ps, zs, Sym2.map_mk]⟩


theorem rlc_twoChannelFullPhysical_exclusiveReflectedLeftEdge_sourceWitness
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {p z : Site 2}
    (hpExclusive :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' p)
    (hpzAdj : (hypercubicLattice 2).Adj p z)
    (hpzTrace : s(p, z) ∈ rlc_reflectedPathEdges gamma'.1) :
    ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      source.1.map Subtype.val = s(p, z) := by
  have hpzFour : s(p, z) ∈
      rlc_connectorFourTraceEdges gamma gamma' := by
    rw [rlc_connectorFourTraceEdges]
    apply Finset.mem_union_right
    rw [rlc_connectorReflectedTraceEdges]
    exact Finset.mem_union_right _ hpzTrace
  have hpBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
    gamma gamma' hpzFour (Sym2.mem_mk_left _ _)
  have hzBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
    gamma gamma' hpzFour (Sym2.mem_mk_right _ _)
  have hpBox : p ∈ rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using
      (rlc_connectorBarrier_mem_connectorBox gamma gamma' hpBarrier)
  have hzBox : z ∈ rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using
      (rlc_connectorBarrier_mem_connectorBox gamma gamma' hzBarrier)
  let ps : RlcConnectorVertex n := ⟨p, hpBox⟩
  let zs : RlcConnectorVertex n := ⟨z, hzBox⟩
  have hreflected : (rlc_connectorReflectedTraceWiring
      gamma gamma').Adj ps zs := by
    refine ⟨hpzAdj, ?_⟩
    rw [rlc_connectorReflectedTraceEdges, Finset.mem_union]
    exact Or.inr (by simpa [ps, zs] using hpzTrace)
  have horiginal : ¬(rlc_connectorTraceWiring gamma gamma').Adj ps zs := by
    rintro ⟨_hAdj, htrace⟩
    rw [Finset.mem_union] at htrace
    rcases htrace with hright | hleft
    · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
      exact hpExclusive.2.2.1 (by simpa [ps] using hends.1)
    · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
      exact hpExclusive.2.2.2 (by simpa [ps] using hends.1)
  have htwo : (rlc_connectorTwoChannelGraph gamma gamma').Adj ps zs :=
    ⟨Or.inr hreflected, horiginal⟩
  let source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
    ⟨s(ps, zs), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
  exact ⟨source, by simp [source, ps, zs, Sym2.map_mk]⟩


theorem
    rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_exclusiveReflectedLeft_traceEdge
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {S : Set (Site 2)}
    {f g : Site 2} (hfg : (faceBoundaryGraph S).Adj f g)
    (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect f))
    (htrace : s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_reflectedPathEdges gamma'.1) :
    RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g := by
  obtain ⟨target, htarget⟩ :=
    rlc_twoChannelFullPhysical_exclusiveReflectedLeftEdge_sourceWitness
      gamma gamma' hfExclusive
        ((rlc_adj_dualReflect f g).mp hfg.1) htrace
  exact ⟨target, htarget⟩


theorem
    rlc_twoChannelFullPhysical_targetBad_not_reflectedLeft_of_exclusive
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {S : Set (Site 2)}
    {f g : Site 2} (hfg : (faceBoundaryGraph S).Adj f g)
    (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect f))
    (hbad : ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
      gamma gamma' f g) :
    s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_reflectedPathEdges gamma'.1 := by
  intro htrace
  exact hbad
    (rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_exclusiveReflectedLeft_traceEdge
      gamma gamma' hfg hfExclusive htrace)


end
end StatMech.Universality
