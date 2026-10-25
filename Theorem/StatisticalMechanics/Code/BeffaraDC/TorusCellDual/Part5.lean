/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellDual.Part5
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


theorem torusCell_euler (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) :
    (Nat.card (ZMod L × ZMod L) : ℤ) - G.edgeSet.ncard +
        torusCellFaceCount L G =
      Nat.card G.ConnectedComponent + 1 - torusCellDefect L G := by
  unfold torusCellDefect
  ring


theorem torusCell_numClusters_dualConfig (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.numClusters (onsTorusGraph L) (torusCellDualConfig L ω) =
      torusCellFaceCount L (FK.openSub (onsTorusGraph L) ω) := by
  unfold FK.numClusters torusCellFaceCount
  rw [← Nat.card_eq_fintype_card]
  exact congrArg (fun G : SimpleGraph (ZMod L × ZMod L) =>
    Nat.card G.ConnectedComponent) (torusCell_openSub_dualConfig L ω)


theorem torusCellFaceCount_bot (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusCellFaceCount L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 1 := by
  unfold torusCellFaceCount
  rw [torusCellDualCutGraph_bot,
    StatMech.Lattice.card_components_eq_one_of_connected hconn]


theorem torusCellFaceCount_full (L : ℕ) [Fact (2 < L)] :
    torusCellFaceCount L (onsTorusGraph L) = L ^ 2 := by
  unfold torusCellFaceCount
  rw [torusCellDualCutGraph_full, StatMech.Lattice.card_components_bot]
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
  ring


theorem torusCellDefect_bot (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusCellDefect L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 0 := by
  unfold torusCellDefect
  rw [torusCellFaceCount_bot L hconn, StatMech.Lattice.card_components_bot]
  simp


theorem torusCellDefect_full (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusCellDefect L (onsTorusGraph L) = 2 := by
  have hedge : (onsTorusGraph L).edgeSet.ncard = 2 * L ^ 2 := by
    rw [Set.ncard_eq_toFinset_card']
    exact onsTorus_card_edges L
  unfold torusCellDefect
  rw [hedge, StatMech.Lattice.card_components_eq_one_of_connected hconn,
    torusCellFaceCount_full]
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
  push_cast
  ring


end StatMech.BeffaraDC
