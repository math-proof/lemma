/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.BeffaraDC.TorusGeometricEuler.Part3
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice (card_components_bot card_components_eq_one_of_connected)

open StatMech.Onsager


theorem geometric_euler_torus (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) :
    (Nat.card (ZMod L × ZMod L) : ℤ) - G.edgeSet.ncard +
        torusGeometricFaceCount L G =
      Nat.card G.ConnectedComponent + 1 - torusGeometricDefect L G := by
  unfold torusGeometricDefect
  ring


theorem geometric_euler_torus_of_defect (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) (δ : ℕ)
    (hδ : torusGeometricDefect L G = δ) :
    (Nat.card (ZMod L × ZMod L) : ℤ) - G.edgeSet.ncard +
        torusGeometricFaceCount L G =
      Nat.card G.ConnectedComponent + 1 - δ := by
  rw [geometric_euler_torus L G, hδ]


theorem torusDualCutGraph_le (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) :
    torusDualCutGraph L G ≤ onsTorusGraph L := fun _ _ h => h.1


theorem torusDualCutGraph_anti (L : ℕ) [Fact (2 < L)]
    {G H : SimpleGraph (ZMod L × ZMod L)} (hGH : G ≤ H) :
    torusDualCutGraph L H ≤ torusDualCutGraph L G := by
  rintro f g ⟨hfg, hclosed⟩
  exact ⟨hfg, fun hopen => hclosed (hGH hopen)⟩


theorem torusGeometricFaceCount_mono (L : ℕ) [Fact (2 < L)]
    {G H : SimpleGraph (ZMod L × ZMod L)} (hGH : G ≤ H) :
    torusGeometricFaceCount L G ≤ torusGeometricFaceCount L H := by
  unfold torusGeometricFaceCount
  exact SimpleGraph.ConnectedComponent.card_le_card_of_le
    (torusDualCutGraph_anti L hGH)


@[simp] theorem torusDualCutGraph_bot (L : ℕ) [Fact (2 < L)] :
    torusDualCutGraph L (⊥ : SimpleGraph (ZMod L × ZMod L)) = onsTorusGraph L := by
  ext f g
  simp [torusDualCutGraph]


theorem torusDualCutGraph_full (L : ℕ) [Fact (2 < L)] :
    torusDualCutGraph L (onsTorusGraph L) = ⊥ := by
  ext f g
  simp only [torusDualCutGraph_adj, bot_adj, iff_false]
  rintro ⟨hfg, hclosed⟩
  exact hclosed ((torusQuarterTurn_adj_iff L f g).2 hfg)


theorem torusGeometricFaceCount_full (L : ℕ) [Fact (2 < L)] :
    torusGeometricFaceCount L (onsTorusGraph L) = L ^ 2 := by
  unfold torusGeometricFaceCount
  rw [torusDualCutGraph_full, card_components_bot]
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
  ring


theorem torusGeometricFaceCount_bot (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusGeometricFaceCount L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 1 := by
  unfold torusGeometricFaceCount
  rw [torusDualCutGraph_bot, card_components_eq_one_of_connected hconn]


theorem torusGeometricDefect_bot (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusGeometricDefect L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 0 := by
  have h := geometric_euler_torus L (⊥ : SimpleGraph (ZMod L × ZMod L))
  rw [torusGeometricFaceCount_bot L hconn, card_components_bot] at h
  simp only [SimpleGraph.edgeSet_bot, Set.ncard_empty, Nat.cast_zero, sub_zero] at h
  norm_num at h
  linarith


theorem torusGeometricDefect_full (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusGeometricDefect L (onsTorusGraph L) = 2 := by
  have hedge : (onsTorusGraph L).edgeSet.ncard = 2 * L ^ 2 := by
    rw [Set.ncard_eq_toFinset_card']
    exact onsTorus_card_edges L
  unfold torusGeometricDefect
  rw [hedge, card_components_eq_one_of_connected hconn, torusGeometricFaceCount_full]
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
  push_cast
  ring

end StatMech.BeffaraDC
