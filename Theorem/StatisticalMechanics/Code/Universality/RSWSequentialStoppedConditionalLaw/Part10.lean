/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part11
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem RlcBookFaithfulTracePair.connectorOriginRegion_mem_strictTopSet
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {z : Site 2} (hz : z ∈ rlc_connectorOriginRegion gamma gamma')
    (hz0 : 0 ≤ z 0) : z ∈ rlc_strictTopSet gamma := by
  have hzSet : z ∈ rlc_connectorOriginRegionSet gamma gamma' := by
    simpa [rlc_connectorOriginRegion] using hz
  obtain ⟨hzAllowed, hoAllowed, hreach⟩ := hzSet
  have hfold := hreach.map (rlc_connectorFoldRightHom gamma gamma')
  have hfoldOrigin : rlc_connectorFoldRight (origin 2) = origin 2 := by
    ext i
    fin_cases i <;> simp [rlc_connectorFoldRight, origin]
  have hfoldZ : rlc_connectorFoldRight z = z := by
    simp [rlc_connectorFoldRight, hz0]
  have horiginZ : (rlc_rightPathAvoidGraph gamma).Reachable
      (origin 2) z := by
    change (rlc_rightPathAvoidGraph gamma).Reachable
      (rlc_connectorFoldRight (origin 2))
      (rlc_connectorFoldRight z) at hfold
    rwa [hfoldOrigin, hfoldZ] at hfold
  obtain ⟨top, htop, htopNot, htopOrigin⟩ :=
    hfaith.origin_mem_strictTopSet
  exact ⟨top, htop, htopNot, htopOrigin.trans horiginZ⟩


theorem RlcBookFaithfulTracePair.connectorOriginRegion_mem_strictBottomSet
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {z : Site 2} (hz : z ∈ rlc_connectorOriginRegion gamma gamma')
    (hz0 : z 0 ≤ 0) : z ∈ rlc_strictBottomSet gamma' := by
  have hzSet : z ∈ rlc_connectorOriginRegionSet gamma gamma' := by
    simpa [rlc_connectorOriginRegion] using hz
  obtain ⟨hzAllowed, hoAllowed, hreach⟩ := hzSet
  have hfold := hreach.map (rlc_connectorFoldLeftHom gamma gamma')
  have hfoldOrigin : rlc_connectorFoldLeft (origin 2) = origin 2 := by
    ext i
    fin_cases i <;> simp [rlc_connectorFoldLeft, origin]
  have hfoldZ : rlc_connectorFoldLeft z = z := by
    simp [rlc_connectorFoldLeft, hz0]
  have horiginZ : (rlc_leftPathAvoidGraph gamma').Reachable
      (origin 2) z := by
    change (rlc_leftPathAvoidGraph gamma').Reachable
      (rlc_connectorFoldLeft (origin 2))
      (rlc_connectorFoldLeft z) at hfold
    rwa [hfoldOrigin, hfoldZ] at hfold
  obtain ⟨bottom, hbottom, hbottomNot, hbottomOrigin⟩ :=
    hfaith.origin_mem_strictBottomSet
  exact ⟨bottom, hbottom, hbottomNot, hbottomOrigin.trans horiginZ⟩


theorem RlcBookFaithfulTracePair.extremalPairCandidateEdges_disjoint_connectorEdges
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    Disjoint (rlc_extremalPairCandidateEdges (gamma, gamma'))
      (rlc_connectorEdges gamma gamma') := by
  rw [Finset.disjoint_left]
  intro e heCandidate heConnector
  have hexplored := rlc_extremalPairCandidateEdges_subset_explored
    gamma gamma' heCandidate
  have hconnector := (Finset.mem_filter.mp heConnector).2
  obtain ⟨z, hzRegion, hzEdge⟩ := hconnector
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [Finset.mem_union] at hexplored
      rw [Sym2.mem_iff] at hzEdge
      rcases hexplored with hright | hleft
      · rw [mem_edgesWithinFinset] at hright
        obtain ⟨u, hu, v, hv, huv⟩ := hright
        have hends : x ∈ rlc_rightExploredVertices gamma ∧
            y ∈ rlc_rightExploredVertices gamma := by
          rw [Sym2.eq_iff] at huv
          rcases huv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
          · subst u
            subst v
            exact ⟨hu, hv⟩
          · subst v
            subst u
            exact ⟨hv, hu⟩
        obtain ⟨hx, hy⟩ := hends
        rw [rlc_rightExploredVertices, Finset.mem_sdiff,
          rlc_mem_rectFinset, mem_rect] at hx hy
        rcases hzEdge with hzEdge | hzEdge
        · subst z
          exact hx.2 (by
            rw [rlc_mem_strictTopVertices]
            exact hfaith.connectorOriginRegion_mem_strictTopSet
              (z := x) hzRegion hx.1.1)
        · subst z
          exact hy.2 (by
            rw [rlc_mem_strictTopVertices]
            exact hfaith.connectorOriginRegion_mem_strictTopSet
              (z := y) hzRegion hy.1.1)
      · rw [mem_edgesWithinFinset] at hleft
        obtain ⟨u, hu, v, hv, huv⟩ := hleft
        have hends : x ∈ rlc_leftExploredVertices gamma' ∧
            y ∈ rlc_leftExploredVertices gamma' := by
          rw [Sym2.eq_iff] at huv
          rcases huv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
          · subst u
            subst v
            exact ⟨hu, hv⟩
          · subst v
            subst u
            exact ⟨hv, hu⟩
        obtain ⟨hx, hy⟩ := hends
        rw [rlc_leftExploredVertices, Finset.mem_sdiff,
          rlc_mem_rectFinset, mem_rect] at hx hy
        rcases hzEdge with hzEdge | hzEdge
        · subst z
          exact hx.2 (by
            rw [rlc_mem_strictBottomVertices]
            exact hfaith.connectorOriginRegion_mem_strictBottomSet
              (z := x) hzRegion hx.1.2.1)
        · subst z
          exact hy.2 (by
            rw [rlc_mem_strictBottomVertices]
            exact hfaith.connectorOriginRegion_mem_strictBottomSet
              (z := y) hzRegion hy.1.2.1)


end
end StatMech.Universality
