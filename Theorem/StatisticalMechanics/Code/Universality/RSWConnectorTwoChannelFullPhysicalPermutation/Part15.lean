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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part15
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalStaticCutIntersection_of_odd_intersection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hodd : ∀ A B : Set (RlcConnectorVertex n),
      (∀ x, rlc_connectorOnRight gamma x → x ∈ A) →
      (∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) →
      (∀ x, rlc_connectorOnRight gamma x → x ∈ B) →
      (∀ y, rlc_connectorOnLeft gamma' y → y ∉ B) →
      Odd (rlc_twoChannelFullPhysicalCutIntersectionTargets
        gamma gamma' A B).card) :
    RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith := by
  classical
  intro A B hAright hAleft hBright hBleft
  have hcard : 0 <
      (rlc_twoChannelFullPhysicalCutIntersectionTargets
        gamma gamma' A B).card := by
    obtain ⟨k, hk⟩ := hodd A B hAright hAleft hBright hBleft
    omega
  obtain ⟨target, htarget⟩ := Finset.card_pos.mp hcard
  have hboth := (Finset.mem_filter.mp htarget).2
  obtain ⟨u, v, hsource, hcrossA⟩ := hboth.1
  obtain ⟨x, y, htargetEdge, hcrossB⟩ := hboth.2
  exact ⟨target, x, y, u, v, htargetEdge, hsource,
    hcrossA, hcrossB⟩


theorem rlc_twoChannelFullPhysicalStaticCutConnectivity_of_cutIntersection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hintersect : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalStaticCutConnectivity
      gamma gamma' hfaith := by
  classical
  intro A hAright hAleft
  let G := rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A
  by_cases hconn : ∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
        G.Reachable x y
  · exact hconn
  · exfalso
    let B : Set (RlcConnectorVertex n) :=
      {z | ∃ x : RlcConnectorVertex n,
        rlc_connectorOnRight gamma x ∧ G.Reachable x z}
    have hBright : ∀ x : RlcConnectorVertex n,
        rlc_connectorOnRight gamma x → x ∈ B := by
      intro x hx
      exact ⟨x, hx, Reachable.refl _⟩
    have hBleft : ∀ y : RlcConnectorVertex n,
        rlc_connectorOnLeft gamma' y → y ∉ B := by
      intro y hy
      rintro ⟨x, hx, hxy⟩
      exact hconn ⟨x, y, hx, hy, hxy⟩
    obtain ⟨target, x, y, u, v, htarget, hsource,
        hcrossA, hcrossB⟩ :=
      hintersect A B hAright hAleft hBright hBleft
    have hxy : G.Adj x y :=
      ⟨target, htarget, u, v, hsource, hcrossA⟩
    rcases hcrossB with ⟨hxB, hyB⟩ | ⟨hyB, hxB⟩
    · obtain ⟨z, hz, hzx⟩ := hxB
      exact hyB ⟨z, hz, hzx.trans hxy.reachable⟩
    · obtain ⟨z, hz, hzy⟩ := hyB
      exact hxB ⟨z, hz, hzy.trans hxy.symm.reachable⟩

theorem rlc_twoChannelFullPhysicalStaticCutIntersection_of_cutConnectivity
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hconnect : RlcTwoChannelFullPhysicalStaticCutConnectivity
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith := by
  intro A B hAright hAleft hBright hBleft
  obtain ⟨x, y, hx, hy, hxy⟩ := hconnect A hAright hAleft
  obtain ⟨w⟩ := hxy
  obtain ⟨p, q, hpq, hpB, hqB⟩ :=
    rlc_walk_pred_first_exit w (fun z => z ∈ B)
      (hBright x hx) (hBleft y hy)
  have hpqAdj := w.adj_of_mem_edges hpq
  obtain ⟨target, htarget, u, v, hsource, hcrossA⟩ := hpqAdj
  exact ⟨target, p, q, u, v, htarget, hsource, hcrossA,
    Or.inl ⟨hpB, hqB⟩⟩

theorem rlc_twoChannelFullPhysicalStaticCutConnectivity_iff_cutIntersection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    RlcTwoChannelFullPhysicalStaticCutConnectivity gamma gamma' hfaith ↔
      RlcTwoChannelFullPhysicalStaticCutIntersection
        gamma gamma' hfaith := by
  constructor
  · exact
      rlc_twoChannelFullPhysicalStaticCutIntersection_of_cutConnectivity
        hfaith
  · exact
      rlc_twoChannelFullPhysicalStaticCutConnectivity_of_cutIntersection
        hfaith


end
end StatMech.Universality
