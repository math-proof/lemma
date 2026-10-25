/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanCoresUnify.Part2
import Instance.StatisticalMechanics.Code.Lattice.JordanCycleSpace
open SimpleGraph Set List Function


namespace StatMech

namespace Lattice

theorem jcs_cycle_nullity_eq_one {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) :
    nullity c.toSubgraph.coe = 1 := by
  classical
  haveI : DecidableEq V := Classical.decEq V
  haveI : Finite ↑c.toSubgraph.verts := jcs_verts_finite c
  have hvcard : Nat.card ↑c.toSubgraph.verts = c.length := by
    rw [c.verts_toSubgraph,
      show {x | x ∈ c.support} = (↑c.support.toFinset : Set V) by ext x; simp,
      Nat.card_coe_set_eq, Set.ncard_coe_finset, jcs_support_card c hc]
  have hecard : c.toSubgraph.coe.edgeSet.ncard = c.length := by
    rw [← Nat.card_coe_set_eq, jcs_coe_edge_card c.toSubgraph,
      c.edgeSet_toSubgraph, Nat.card_coe_set_eq, jcs_walk_edgeSet_ncard c hc]
  have hccard : Nat.card c.toSubgraph.coe.ConnectedComponent = 1 :=
    card_components_eq_one_of_connected (Subgraph.connected_iff'.mp c.toSubgraph_connected)
  have h3 := hc.three_le_length
  unfold nullity
  rw [hccard, hecard, hvcard]
  omega


theorem jcs_cycle_faceCount_eq_two {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) :
    faceCount c.toSubgraph.coe = 2 := by
  unfold faceCount; rw [jcs_cycle_nullity_eq_one c hc]


theorem jcs_cycle_euler {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) :
    (Nat.card ↑c.toSubgraph.verts : ℤ) - c.toSubgraph.coe.edgeSet.ncard + 2
      = 1 + Nat.card c.toSubgraph.coe.ConnectedComponent := by
  classical
  haveI : DecidableEq ↑c.toSubgraph.verts := Classical.decEq _
  have h := euler_general c.toSubgraph.coe
  rw [jcs_cycle_faceCount_eq_two c hc] at h
  exact_mod_cast h


theorem jcs_two_components_of_sides (S : Set (Site 2)) {x y : Site 2} (hx : x ∈ S) (hy : y ∉ S)
    (hin : ∀ a b : Site 2, a ∈ S → b ∈ S → (latticeMinusBarrier S).Reachable a b)
    (hout : ∀ a b : Site 2, a ∉ S → b ∉ S → (latticeMinusBarrier S).Reachable a b) :
    Nat.card (latticeMinusBarrier S).ConnectedComponent = 2 := by
  classical
  set L := latticeMinusBarrier S with hL
  let f : L.ConnectedComponent → Bool :=
    ConnectedComponent.lift (fun a => decide (a ∈ S)) (by
      intro a b p _
      have : (a ∈ S ↔ b ∈ S) := barrier_sameSide_of_reachable S ⟨p⟩
      simp only [decide_eq_decide]; exact this)
  have hf_mk : ∀ a : Site 2, f (L.connectedComponentMk a) = decide (a ∈ S) := fun _ => rfl
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · refine ConnectedComponent.ind₂ ?_
      intro a b hab
      rw [hf_mk, hf_mk, decide_eq_decide] at hab
      rw [ConnectedComponent.eq]
      by_cases haS : a ∈ S
      · exact hin a b haS (hab.mp haS)
      · exact hout a b haS (fun hbS => haS (hab.mpr hbS))
    · intro c
      cases c with
      | true => exact ⟨L.connectedComponentMk x, by rw [hf_mk]; simp [hx]⟩
      | false => exact ⟨L.connectedComponentMk y, by rw [hf_mk]; simp [hy]⟩
  rw [Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_bool]


end Lattice
end StatMech
