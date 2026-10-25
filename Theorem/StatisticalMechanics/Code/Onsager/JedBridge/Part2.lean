/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.InsideClimb.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Def.StatisticalMechanics.Code.Onsager.JedBridge.Part2


namespace StatMech.Onsager.JedBridge

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.WalkCrossing
  StatMech.Onsager.NoDoubleWind StatMech.Onsager.JordanParity StatMech.Onsager.InsideClimb

open StatMech.Lattice

open SimpleGraph


theorem cycleGraph_card_components_one (m : ℕ) :
    Nat.card (cycleGraph (m + 3)).ConnectedComponent = 1 := by
  have hconn : (cycleGraph (m + 3)).Connected := cycleGraph_connected
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun c c' => ?_⟩, ⟨(cycleGraph (m + 3)).connectedComponentMk 0⟩⟩
  induction c using ConnectedComponent.ind with
  | _ u =>
    induction c' using ConnectedComponent.ind with
    | _ v => exact ConnectedComponent.sound (hconn.preconnected u v)


theorem cycleGraph_card_edges (m : ℕ) :
    (cycleGraph (m + 3)).edgeSet.ncard = m + 3 := by
  have hsum : ∑ v : Fin (m + 3), (cycleGraph (m + 3)).degree v
      = 2 * (cycleGraph (m + 3)).edgeFinset.card :=
    (cycleGraph (m + 3)).sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v : Fin (m + 3), (cycleGraph (m + 3)).degree v = 2 :=
    fun v => cycleGraph_degree_three_le
  rw [Finset.sum_congr rfl (fun v _ => hdeg v), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum
  have hcard : (cycleGraph (m + 3)).edgeFinset.card = m + 3 := by omega
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hcard]


theorem cycle_nullity_one (m : ℕ) : nullity (cycleGraph (m + 3)) = 1 := by
  unfold nullity
  rw [cycleGraph_card_edges m, cycleGraph_card_components_one m,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  omega


theorem walkSubgraph_nullity_one {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    nullity (walkSubgraph d hclosed hsimple).G = 1 := by
  show nullity (cycleGraph (m + 3)) = 1
  exact cycle_nullity_one m


theorem walk_one_bounded_region {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    Nat.card {c : (whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).ConnectedComponent
      // c.supp.Finite} = 1 := by
  obtain ⟨e⟩ := jed_faithfulDiscreteJordan (walkSubgraph d hclosed hsimple)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin,
    walkSubgraph_nullity_one d hclosed hsimple]


theorem walk_faithfulRegionCount_one {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    whc_faithfulRegionCount (walkSubgraph d hclosed hsimple) = 1 :=
  walk_one_bounded_region d hclosed hsimple


end StatMech.Onsager.JedBridge
