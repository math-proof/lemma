/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part7
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

@[simp] theorem pfdOuterLeafCollapse_lift (P : PlanarZ2Subgraph)
    (C : kwg_Face P) :
    pfdOuterLeafCollapse P (pfdOuterLeafLift P C) = C := by
  unfold pfdOuterLeafLift
  split
  · simpa [pfdOuterLeafCollapse] using ‹C = pfdOuterFace P›.symm
  · rfl


theorem pfdOuterLeaf_reachable_of_collapse_eq (P : PlanarZ2Subgraph)
    (F : Set (kwg_Edge P)) {x y : pfdOuterLeafVertex P}
    (hxy : pfdOuterLeafCollapse P x = pfdOuterLeafCollapse P y) :
    (pfdOuterLeafWiredGraph P F).Reachable x y := by
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          have hsub : x = y := Subtype.ext hxy
          subst y
          exact ⟨Walk.nil⟩
      | inr y =>
          exfalso
          exact x.2 hxy
  | inr x =>
      cases y with
      | inl y =>
          exfalso
          exact y.2 hxy.symm
      | inr y =>
          by_cases h : Sum.inr x = (Sum.inr y : pfdOuterLeafVertex P)
          · exact h ▸ ⟨Walk.nil⟩
          · exact (pfdOuterLeafWiredGraph_adj P F _ _).2
              (Or.inr ⟨h, by cases x <;> trivial, by cases y <;> trivial⟩) |>.reachable


theorem pfdOuterLeaf_collapse_reachable_of_adj (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) {x y : pfdOuterLeafVertex P}
    (hxy : (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).Adj x y) :
    (pfdClosedDual P K).Reachable
      (pfdOuterLeafCollapse P x) (pfdOuterLeafCollapse P y) := by
  rw [pfdOuterLeafWiredGraph_adj] at hxy
  rcases hxy with hopen | hboundary
  · obtain ⟨_, e, heK, heends⟩ := hopen
    by_cases heq : pfdOuterLeafCollapse P x = pfdOuterLeafCollapse P y
    · simpa [heq]
    · apply SimpleGraph.Adj.reachable
      rw [pfdClosedDual_adj]
      refine ⟨heq, e, heK, ?_⟩
      have hmap := congrArg (Sym2.map (pfdOuterLeafCollapse P)) heends
      rw [pfdOuterLeafEnds_collapse] at hmap
      simpa using hmap
  · have hx : pfdOuterLeafCollapse P x = pfdOuterFace P := by
      cases x <;> simp_all [pfdOuterLeafBoundary, pfdOuterLeafCollapse]
    have hy : pfdOuterLeafCollapse P y = pfdOuterFace P := by
      cases y <;> simp_all [pfdOuterLeafBoundary, pfdOuterLeafCollapse]
    simpa [hx, hy]


theorem pfdOuterLeaf_collapse_reachable (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) {x y : pfdOuterLeafVertex P}
    (hxy : (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).Reachable x y) :
    (pfdClosedDual P K).Reachable
      (pfdOuterLeafCollapse P x) (pfdOuterLeafCollapse P y) := by
  rcases hxy with ⟨w⟩
  induction w with
  | nil => exact ⟨Walk.nil⟩
  | cons h w ih =>
      exact (pfdOuterLeaf_collapse_reachable_of_adj P K h).trans ih


theorem pfdOuterLeaf_reachable_of_dualAdj (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) {x y : pfdOuterLeafVertex P}
    (hxy : (pfdClosedDual P K).Adj
      (pfdOuterLeafCollapse P x) (pfdOuterLeafCollapse P y)) :
    (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).Reachable x y := by
  obtain ⟨hne, e, heK, heends⟩ := (pfdClosedDual_adj P K _ _).mp hxy
  let u := pfdOuterLeafEndpoint P e false
  let v := pfdOuterLeafEndpoint P e true
  have huvCollapse :
      s(pfdOuterLeafCollapse P u, pfdOuterLeafCollapse P v) =
        s(pfdOuterLeafCollapse P x, pfdOuterLeafCollapse P y) := by
    rw [← heends, ← pfdOuterLeafEnds_collapse]
    rfl
  have huvNe : u ≠ v := by
    intro huv
    apply hne
    rw [huv] at huvCollapse
    rw [Sym2.eq_iff] at huvCollapse
    rcases huvCollapse with h | h
    · exact h.1.symm.trans h.2
    · exact h.2.symm.trans h.1
  have hedge : (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).Adj u v := by
    rw [pfdOuterLeafWiredGraph_adj]
    exact Or.inl ⟨huvNe, e, heK, rfl⟩
  rw [Sym2.eq_iff] at huvCollapse
  rcases huvCollapse with hs | hs
  · exact (pfdOuterLeaf_reachable_of_collapse_eq P _ hs.1.symm).trans
      (hedge.reachable.trans
        (pfdOuterLeaf_reachable_of_collapse_eq P _ hs.2))
  · exact (pfdOuterLeaf_reachable_of_collapse_eq P _ hs.2.symm).trans
      (hedge.symm.reachable.trans
        (pfdOuterLeaf_reachable_of_collapse_eq P _ hs.1))


theorem pfdOuterLeaf_lift_reachable_of_dual (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) {C D : kwg_Face P}
    (hCD : (pfdClosedDual P K).Reachable C D) :
    (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).Reachable
        (pfdOuterLeafLift P C) (pfdOuterLeafLift P D) := by
  rcases hCD with ⟨w⟩
  induction w with
  | nil => exact ⟨Walk.nil⟩
  | @cons A B C hAB w ih =>
      exact (pfdOuterLeaf_reachable_of_dualAdj P K
        (x := pfdOuterLeafLift P A) (y := pfdOuterLeafLift P B)
        (by simpa using hAB)).trans ih


theorem pfdOuterLeaf_reachable_iff_dual (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) {x y : pfdOuterLeafVertex P} :
    (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).Reachable x y ↔
    (pfdClosedDual P K).Reachable
      (pfdOuterLeafCollapse P x) (pfdOuterLeafCollapse P y) := by
  constructor
  · exact pfdOuterLeaf_collapse_reachable P K
  · intro hxy
    exact (pfdOuterLeaf_reachable_of_collapse_eq P _
      (pfdOuterLeafCollapse_lift P _).symm).trans
      ((pfdOuterLeaf_lift_reachable_of_dual P K hxy).trans
        (pfdOuterLeaf_reachable_of_collapse_eq P _
          (pfdOuterLeafCollapse_lift P _)))


end
end StatMech.FrontierD
