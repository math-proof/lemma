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
import Structure.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem pairedEdgeCutIntersection_of_hexCutCarrier
    {V I : Type*} (source target : I → Sym2 V) (R L : Set V)
    (hcarrier : ∀ A B : Set V,
      R ⊆ A → L ∩ A = ∅ → R ⊆ B → L ∩ B = ∅ →
        Nonempty (PairedEdgeHexCutCarrier source target A B)) :
    PairedEdgeCutIntersection source target R L := by
  intro A B hRA hLA hRB hLB
  obtain ⟨C⟩ := hcarrier A B hRA hLA hRB hLB
  have hsep : Lattice.ArcSeparatingSet
      {z : Site 2 | z ∈ C.vertical.support}
      C.alpha C.beta C.bottomRow C.topRow :=
    Lattice.jec_arcSeparatingSet
      C.alpha C.beta C.bottomRow C.topRow C.bottomX C.topX
      C.alpha_lt_beta C.bottomRow_le_topRow C.bottomX_lower C.bottomX_upper
      C.topX_lower C.topX_upper C.vertical C.vertical_mem
      {z : Site 2 | z ∈ C.vertical.support} (by
        intro z hz
        exact hz)
  obtain ⟨z, hzHorizontal, hzVertical⟩ :=
    Lattice.tpc_two_paths_cross_of_sep hsep
      C.horizontalStart_mem C.horizontalEnd_mem
      C.horizontalStart_left C.horizontalEnd_right
      C.horizontal C.horizontal_mem
  exact C.intersection_pair z hzHorizontal hzVertical


theorem rlc_twoChannelFullPhysicalStaticCutIntersection_iff_pairedEdge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith ↔
      PairedEdgeCutIntersection
        (fun target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ↦
          (rlc_twoChannelFullPhysicalSourceEdge target).1)
        (fun target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ↦
          target.1.1)
        {x | rlc_connectorOnRight gamma x}
        {x | rlc_connectorOnLeft gamma' x} := by
  constructor
  · intro hcut A B hAright hAleft hBright hBleft
    obtain ⟨target, x, y, u, v, htarget, hsource, hcrossA, hcrossB⟩ :=
      hcut A B hAright (by
        intro y hy hyA
        have : y ∈ ({x | rlc_connectorOnLeft gamma' x} :
          Set (RlcConnectorVertex n)) ∩ A := ⟨hy, hyA⟩
        have hempty : y ∈ (∅ : Set (RlcConnectorVertex n)) := hAleft ▸ this
        exact hempty) hBright (by
          intro y hy hyB
          have : y ∈ ({x | rlc_connectorOnLeft gamma' x} :
            Set (RlcConnectorVertex n)) ∩ B := ⟨hy, hyB⟩
          have hempty : y ∈ (∅ : Set (RlcConnectorVertex n)) := hBleft ▸ this
          exact hempty)
    exact ⟨target, ⟨u, v, hsource, hcrossA⟩,
      x, y, htarget, hcrossB⟩
  · intro hpaired A B hAright hAleft hBright hBleft
    obtain ⟨target, ⟨u, v, hsource, hcrossA⟩,
        x, y, htarget, hcrossB⟩ :=
      hpaired A B hAright (by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        exact fun h ↦ hAleft z h.1 h.2) hBright (by
          ext z
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
            iff_false]
          exact fun h ↦ hBleft z h.1 h.2)
    exact ⟨target, x, y, u, v, htarget, hsource, hcrossA, hcrossB⟩


theorem rlc_twoChannelFullPhysicalStaticCutIntersection_iff_twoColorHex
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith ↔
      PairedEdgeTwoColorHexAlternative
        (fun target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ↦
          (rlc_twoChannelFullPhysicalSourceEdge target).1)
        (fun target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ↦
          target.1.1)
        {x | rlc_connectorOnRight gamma x}
        {x | rlc_connectorOnLeft gamma' x} := by
  rw [rlc_twoChannelFullPhysicalStaticCutIntersection_iff_pairedEdge hfaith,
    pairedEdgeCutIntersection_iff_twoColorHexAlternative]


theorem rlc_twoChannelFullPhysicalStaticCutIntersection_of_hexCutCarrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hcarrier : ∀ A B : Set (RlcConnectorVertex n),
      {x | rlc_connectorOnRight gamma x} ⊆ A →
      {x | rlc_connectorOnLeft gamma' x} ∩ A = ∅ →
      {x | rlc_connectorOnRight gamma x} ⊆ B →
      {x | rlc_connectorOnLeft gamma' x} ∩ B = ∅ →
      Nonempty (PairedEdgeHexCutCarrier
        (fun target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ↦
          (rlc_twoChannelFullPhysicalSourceEdge target).1)
        (fun target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ↦
          target.1.1) A B)) :
    RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith := by
  rw [rlc_twoChannelFullPhysicalStaticCutIntersection_iff_pairedEdge hfaith]
  exact pairedEdgeCutIntersection_of_hexCutCarrier _ _ _ _ hcarrier


end
end StatMech.Universality
