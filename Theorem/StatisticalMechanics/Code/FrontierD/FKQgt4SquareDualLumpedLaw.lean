/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualBundles.Part2
import Theorem.StatisticalMechanics.Code.FK.IndexedEdgeLumping.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualLumpedLaw
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

@[simp] theorem pfdEdgeComplement_apply (P : PlanarZ2Subgraph)
    (omega : ConfigSpace P.G.edgeSet) (e : P.G.edgeSet) :
    pfdEdgeComplement P omega e = !(omega e) := rfl

@[simp] theorem pfdEdgeComplement_symm_apply (P : PlanarZ2Subgraph)
    (omega : ConfigSpace P.G.edgeSet) (e : P.G.edgeSet) :
    (pfdEdgeComplement P).symm omega e = !(omega e) := rfl

@[simp] theorem pfdEdgeComplement_involutive (P : PlanarZ2Subgraph)
    (omega : ConfigSpace P.G.edgeSet) :
    pfdEdgeComplement P (pfdEdgeComplement P omega) = omega := by
  funext e
  simp

theorem openCount_complement {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (omega : ConfigSpace (Sym2 V)) :
    openCount G (fun e => !(omega e)) = G.edgeFinset.card - openCount G omega := by
  have hclosed : openCount G (fun e => !(omega e)) = closedCount G omega := by
    unfold openCount closedCount
    congr 1
    ext e
    simp only [Finset.mem_filter]
    cases omega e <;> simp
  rw [hclosed]
  have hsum := openCount_add_closedCount G omega
  omega

theorem mem_openSub_edgeSet_iff_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (omega : ConfigSpace (Sym2 V)) {e : Sym2 V}
    (he : e ∈ G.edgeSet) :
    e ∈ (openSub G omega).edgeSet ↔ omega e = true := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, openSub_adj]
      rw [SimpleGraph.mem_edgeSet] at he
      simp [he]


theorem pfdDualEdgeProduct_eq_indexed (P : PlanarZ2Subgraph)
    (p : Real) (omega : ConfigSpace (Sym2 P.V)) :
    edgeProductCount p P.G.edgeFinset.card
        (P.G.edgeFinset.card - (openSub P.G omega).edgeSet.ncard) =
      indexedBernoulliWeight p
        (fun e : kwg_Edge P => !(omega e.1)) := by
  rw [pfd_openSub_edge_ncard]
  calc
    edgeProductCount p P.G.edgeFinset.card
        (P.G.edgeFinset.card - openCount P.G omega) =
        edgeProductCount p P.G.edgeFinset.card
          (openCount P.G (fun e => !(omega e))) := by
      rw [openCount_complement]
    _ = edgeProduct P.G p (fun e => !(omega e)) :=
      (dlt_edgeProduct_eq_count P.G p (fun e => !(omega e))).symm
    _ = indexedBernoulliWeight p
        (fun e : kwg_Edge P => !(omega e.1)) := by
      unfold edgeProduct indexedBernoulliWeight
      rw [← Finset.prod_attach P.G.edgeFinset]
      rw [Finset.attach_eq_univ]
      let edgeEquiv : P.G.edgeFinset ≃ kwg_Edge P :=
        { toFun := fun e => ⟨e.1, by simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
          invFun := fun e => ⟨e.1, by simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
          left_inv := by intro e; rfl
          right_inv := by intro e; rfl }
      apply Fintype.prod_equiv edgeEquiv
      intro e
      rfl


theorem pfdClosedDual_eq_openSub_indexedSupport (P : PlanarZ2Subgraph)
    (omega : ConfigSpace (Sym2 P.V)) :
    pfdClosedDual P (openSub P.G omega) =
      openSub (pfdClosedDual P ⊥)
        (extendActive (pfdClosedDual P ⊥)
          (pfdIndexedSupportActive P
            (fun e : kwg_Edge P => !(omega e.1)))) := by
  ext C D
  rw [pfdClosedDual_adj, openSub_adj]
  constructor
  · rintro ⟨hne, e, heclosed, hends⟩
    have hfull : (pfdClosedDual P ⊥).Adj C D :=
      (pfdClosedDual_adj P ⊥ C D).2 ⟨hne, e, by simp, hends⟩
    refine ⟨hfull, ?_⟩
    let a : (pfdClosedDual P ⊥).edgeSet :=
      ⟨s(C, D), by simpa [SimpleGraph.mem_edgeSet] using hfull⟩
    change extendActive (pfdClosedDual P ⊥)
      (pfdIndexedSupportActive P
        (fun e : kwg_Edge P => !(omega e.1))) a.1 = true
    rw [extendActive_apply]
    simp only [pfdIndexedSupportActive, restrictActive,
      indexedBundleSupport, decide_eq_true_eq]
    refine ⟨e, hends, ?_⟩
    have hnot : omega e.1 ≠ true := by
      intro hopen
      exact heclosed ((mem_openSub_edgeSet_iff_of_mem P.G omega e.2).2 hopen)
    cases homega : omega e.1 <;> simp_all
  · rintro ⟨hfull, hopen⟩
    have hfullEdge : s(C, D) ∈ (pfdClosedDual P ⊥).edgeSet := by
      simpa [SimpleGraph.mem_edgeSet] using hfull
    let a : (pfdClosedDual P ⊥).edgeSet := ⟨s(C, D), hfullEdge⟩
    change extendActive (pfdClosedDual P ⊥)
      (pfdIndexedSupportActive P
        (fun e : kwg_Edge P => !(omega e.1))) a.1 = true at hopen
    rw [extendActive_apply] at hopen
    rw [pfdClosedDual_adj] at hfull
    obtain ⟨hne, _, _, _⟩ := hfull
    simp only [pfdIndexedSupportActive, restrictActive,
      indexedBundleSupport, decide_eq_true_eq] at hopen
    obtain ⟨e, hends, heopen⟩ := hopen
    refine ⟨hne, e, ?_, hends⟩
    intro hmem
    have hopenPrimal :=
      (mem_openSub_edgeSet_iff_of_mem P.G omega e.2).1 hmem
    cases h : omega e.1 <;> simp_all


theorem pfdDualWeight_eq_indexedSupport (P : PlanarZ2Subgraph)
    (p q : Real) (omega : ConfigSpace (Sym2 P.V)) :
    pfdDualWeight P p q (openSub P.G omega) =
      indexedBernoulliWeight p
          (fun e : kwg_Edge P => !(omega e.1)) *
        q ^ (numClustersBC (pfdClosedDual P ⊥) ⊥
          (extendActive (pfdClosedDual P ⊥)
            (pfdIndexedSupportActive P
              (fun e : kwg_Edge P => !(omega e.1))))) := by
  unfold pfdDualWeight
  rw [pfdDualEdgeProduct_eq_indexed]
  congr 1
  unfold numClustersBC
  rw [sup_bot_eq, ← pfdClosedDual_eq_openSub_indexedSupport]


end
end StatMech.FrontierD
