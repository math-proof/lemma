/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CoeffMatch
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.Onsager.TorusSpinSectors


namespace StatMech.Onsager

open StatMech.Ising


theorem ons_evenHomology_union (L : ℕ)
    (F G : Finset (Sym2 (ZMod L × ZMod L))) (hdisj : Disjoint F G) :
    ons_evenHomology L (F ∪ G) =
      ons_evenHomology L F + ons_evenHomology L G := by
  classical
  apply Prod.ext
  · apply Fin.ext
    change ((F ∪ G).filter (ons_xSeamEdge L)).card % 2 =
      (((F.filter (ons_xSeamEdge L)).card % 2) +
        ((G.filter (ons_xSeamEdge L)).card % 2)) % 2
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      Nat.add_mod]
  · apply Fin.ext
    change ((F ∪ G).filter (ons_ySeamEdge L)).card % 2 =
      (((F.filter (ons_ySeamEdge L)).card % 2) +
        ((G.filter (ons_ySeamEdge L)).card % 2)) % 2
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      Nat.add_mod]

theorem ons_evenHomology_biUnion
    {L : ℕ} {iota : Type*} [DecidableEq iota]
    (S : Finset iota)
    (piece : iota → Finset (Sym2 (ZMod L × ZMod L)))
    (hdisj : (S : Set iota).PairwiseDisjoint piece) :
    ons_evenHomology L (S.biUnion piece) =
      ∑ i ∈ S, ons_evenHomology L (piece i) := by
  induction S using Finset.induction_on with
  | empty =>
      simp [ons_evenHomology]
  | @insert a S ha ih =>
      have hdisjS : (S : Set iota).PairwiseDisjoint piece := by
        intro i hi j hj hij
        exact hdisj (by simp [hi]) (by simp [hj]) hij
      have haS : Disjoint (piece a) (S.biUnion piece) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj (by simp) (by simp [hj]) (by
          intro haj
          subst j
          exact ha hj)
      rw [Finset.biUnion_insert, ons_evenHomology_union L _ _ haS,
        Finset.sum_insert ha, ih hdisjS]

end StatMech.Onsager
