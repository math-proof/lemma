/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part6
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

namespace FKIsingDobrushinMedialComplex

variable {P : PlanarZ2Subgraph} (C : FKIsingDobrushinMedialComplex P)


theorem mem_exploration_iff (omega : ConfigSpace (Sym2 P.V))
    (d : FKIsingMedialDart P) :
    d ∈ C.exploration omega ↔
      (C.loopGraph omega).Reachable C.sourceDart d := by
  simp [exploration, explorationFinset]

theorem source_mem_exploration (omega : ConfigSpace (Sym2 P.V)) :
    C.sourceDart ∈ C.exploration omega := by
  rw [C.mem_exploration_iff]

theorem localMate_mem_exploration_iff
    (omega : ConfigSpace (Sym2 P.V)) (d : FKIsingMedialDart P) :
    FKIsingMedialDart.localMate omega d ∈ C.exploration omega ↔
      d ∈ C.exploration omega := by
  rw [C.mem_exploration_iff, C.mem_exploration_iff]
  have hadj : (C.loopGraph omega).Adj d
      (FKIsingMedialDart.localMate omega d) := Or.inl rfl
  exact ⟨fun h => h.trans hadj.symm.reachable,
    fun h => h.trans hadj.reachable⟩

theorem closed_west_mem_iff_south (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    (e, .west) ∈ C.exploration (setClosed e.1 omega) ↔
      (e, .south) ∈ C.exploration (setClosed e.1 omega) := by
  have h := C.localMate_mem_exploration_iff (setClosed e.1 omega) (e, .west)
  simpa [FKIsingMedialDart.localMate] using h.symm

theorem closed_east_mem_iff_north (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    (e, .east) ∈ C.exploration (setClosed e.1 omega) ↔
      (e, .north) ∈ C.exploration (setClosed e.1 omega) := by
  have h := C.localMate_mem_exploration_iff (setClosed e.1 omega) (e, .east)
  simpa [FKIsingMedialDart.localMate] using h.symm

theorem open_west_mem_iff_north (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    (e, .west) ∈ C.exploration (setOpen e.1 omega) ↔
      (e, .north) ∈ C.exploration (setOpen e.1 omega) := by
  have h := C.localMate_mem_exploration_iff (setOpen e.1 omega) (e, .west)
  simpa [FKIsingMedialDart.localMate] using h.symm

theorem open_east_mem_iff_south (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    (e, .east) ∈ C.exploration (setOpen e.1 omega) ↔
      (e, .south) ∈ C.exploration (setOpen e.1 omega) := by
  have h := C.localMate_mem_exploration_iff (setOpen e.1 omega) (e, .east)
  simpa [FKIsingMedialDart.localMate] using h.symm


theorem loopGraph_setOpen_eq_twoEdgeSwitch
    (omega : ConfigSpace (Sym2 P.V)) (e : FKIsingMedialVertex P) :
    C.loopGraph (setOpen e.1 omega) =
      medialTwoEdgeSwitch (C.loopGraph (setClosed e.1 omega))
        (e, .west) (e, .south) (e, .east) (e, .north) := by
  have hbW : C.bondMate (e, .west) ≠ (e, .south) := by
    simpa [FKIsingMedialDart.localMate] using
      C.bondMate_ne_localMate (setClosed e.1 omega) (e, .west)
  have hbS : C.bondMate (e, .south) ≠ (e, .west) := by
    simpa [FKIsingMedialDart.localMate] using
      C.bondMate_ne_localMate (setClosed e.1 omega) (e, .south)
  have hbE : C.bondMate (e, .east) ≠ (e, .north) := by
    simpa [FKIsingMedialDart.localMate] using
      C.bondMate_ne_localMate (setClosed e.1 omega) (e, .east)
  have hbN : C.bondMate (e, .north) ≠ (e, .east) := by
    simpa [FKIsingMedialDart.localMate] using
      C.bondMate_ne_localMate (setClosed e.1 omega) (e, .north)
  have hbWr : (e, .south) ≠ C.bondMate (e, .west) := Ne.symm hbW
  have hbSr : (e, .west) ≠ C.bondMate (e, .south) := Ne.symm hbS
  have hbEr : (e, .north) ≠ C.bondMate (e, .east) := Ne.symm hbE
  have hbNr : (e, .east) ≠ C.bondMate (e, .north) := Ne.symm hbN
  have hlocal_of_ne (d : FKIsingMedialVertex P) (hd : d ≠ e)
      (side : FKIsingMedialSide) :
      FKIsingMedialDart.localMate (setOpen e.1 omega) (d, side) =
        FKIsingMedialDart.localMate (setClosed e.1 omega) (d, side) := by
    have hde : d.1 ≠ e.1 := by
      intro h
      exact hd (Subtype.ext h)
    cases h : omega d.1 <;> cases side <;>
      simp [FKIsingMedialDart.localMate, setOpen, setClosed,
        Function.update_of_ne hde, h]
  ext d f
  rcases d with ⟨d, ds⟩
  rcases f with ⟨f, fs⟩
  by_cases hd : d = e <;> by_cases hf : f = e
  · subst d
    subst f
    cases ds <;> cases fs <;>
      simp [loopGraph, medialTwoEdgeSwitch, FKIsingMedialDart.localMate,
        SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
        SimpleGraph.edge_adj, hbWr, hbNr, hbEr, hbSr]
  · subst d
    cases ds <;>
      simp [loopGraph, medialTwoEdgeSwitch, FKIsingMedialDart.localMate,
        SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
        SimpleGraph.edge_adj, hf]
  · subst f
    have hlocal := hlocal_of_ne d hd ds
    cases fs <;>
      simp [loopGraph, medialTwoEdgeSwitch, hlocal,
        SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
        SimpleGraph.edge_adj, hd]
  · have hlocal := hlocal_of_ne d hd ds
    have hold : s((d, ds), (f, fs)) ∉
        ({s((e, .west), (e, .south)), s((e, .east), (e, .north))} :
          Set (Sym2 (FKIsingMedialDart P))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor <;> intro h
      · rcases Sym2.eq_iff.mp h with h | h
        · exact hd (Prod.mk.inj h.1).1
        · exact hd (Prod.mk.inj h.1).1
      · rcases Sym2.eq_iff.mp h with h | h
        · exact hd (Prod.mk.inj h.1).1
        · exact hd (Prod.mk.inj h.1).1
    change ((f, fs) = FKIsingMedialDart.localMate (setOpen e.1 omega) (d, ds) ∨
        (f, fs) = C.bondMate (d, ds)) ↔ _
    rw [medialTwoEdgeSwitch, SimpleGraph.sup_adj, SimpleGraph.sup_adj,
      SimpleGraph.deleteEdges_adj]
    simp only [loopGraph]
    rw [hlocal]
    simp [hold, SimpleGraph.edge_adj, hd, hf]


theorem open_local_mem_of_closed_west_mem_not_east
    (omega : ConfigSpace (Sym2 P.V)) (e : FKIsingMedialVertex P)
    (hwest : (e, .west) ∈ C.exploration (setClosed e.1 omega))
    (heast : (e, .east) ∉ C.exploration (setClosed e.1 omega)) :
    forall side, (e, side) ∈ C.exploration (setOpen e.1 omega) := by
  let G := C.loopGraph (setClosed e.1 omega)
  have hsourceWest : G.Reachable C.sourceDart (e, .west) :=
    (C.mem_exploration_iff _ _).1 hwest
  have hwestEast : ¬ G.Reachable (e, .west) (e, .east) := by
    intro h
    exact heast ((C.mem_exploration_iff _ _).2 (hsourceWest.trans h))
  have hwestSouth : G.Adj (e, .west) (e, .south) := by
    exact Or.inl (by simp [FKIsingMedialDart.localMate])
  have heastNorth : G.Adj (e, .east) (e, .north) := by
    exact Or.inl (by simp [FKIsingMedialDart.localMate])
  have heven : forall d, Even (G.degree d) := by
    intro d
    rw [C.loopGraph_degree_eq_two]
    exact even_two
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_left G heven
    hwestSouth heastNorth hwestEast hsourceWest
  rw [← C.loopGraph_setOpen_eq_twoEdgeSwitch omega e] at hall
  intro side
  rw [C.mem_exploration_iff]
  cases side
  · exact hall.1
  · exact hall.2.2.1
  · exact hall.2.1
  · exact hall.2.2.2


theorem open_local_mem_of_closed_east_mem_not_west
    (omega : ConfigSpace (Sym2 P.V)) (e : FKIsingMedialVertex P)
    (heast : (e, .east) ∈ C.exploration (setClosed e.1 omega))
    (hwest : (e, .west) ∉ C.exploration (setClosed e.1 omega)) :
    forall side, (e, side) ∈ C.exploration (setOpen e.1 omega) := by
  let G := C.loopGraph (setClosed e.1 omega)
  have hsourceEast : G.Reachable C.sourceDart (e, .east) :=
    (C.mem_exploration_iff _ _).1 heast
  have hwestEast : ¬ G.Reachable (e, .west) (e, .east) := by
    intro h
    exact hwest ((C.mem_exploration_iff _ _).2
      (hsourceEast.trans h.symm))
  have hwestSouth : G.Adj (e, .west) (e, .south) := by
    exact Or.inl (by simp [FKIsingMedialDart.localMate])
  have heastNorth : G.Adj (e, .east) (e, .north) := by
    exact Or.inl (by simp [FKIsingMedialDart.localMate])
  have heven : forall d, Even (G.degree d) := by
    intro d
    rw [C.loopGraph_degree_eq_two]
    exact even_two
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_right G heven
    hwestSouth heastNorth hwestEast hsourceEast
  rw [← C.loopGraph_setOpen_eq_twoEdgeSwitch omega e] at hall
  intro side
  rw [C.mem_exploration_iff]
  cases side
  · exact hall.1
  · exact hall.2.2.1
  · exact hall.2.1
  · exact hall.2.2.2


theorem open_local_not_mem_of_closed_west_east_not_mem
    (omega : ConfigSpace (Sym2 P.V)) (e : FKIsingMedialVertex P)
    (hwest : (e, .west) ∉ C.exploration (setClosed e.1 omega))
    (heast : (e, .east) ∉ C.exploration (setClosed e.1 omega)) :
    forall side, (e, side) ∉ C.exploration (setOpen e.1 omega) := by
  let G := C.loopGraph (setClosed e.1 omega)
  have hsourceWest : ¬ G.Reachable C.sourceDart (e, .west) := by
    simpa only [G, ← C.mem_exploration_iff] using hwest
  have hsourceEast : ¬ G.Reachable C.sourceDart (e, .east) := by
    simpa only [G, ← C.mem_exploration_iff] using heast
  have hwestSouth : G.Adj (e, .west) (e, .south) := by
    exact Or.inl (by simp [FKIsingMedialDart.localMate])
  have heastNorth : G.Adj (e, .east) (e, .north) := by
    exact Or.inl (by simp [FKIsingMedialDart.localMate])
  have hiff (d : FKIsingMedialDart P) :
      (C.loopGraph (setOpen e.1 omega)).Reachable C.sourceDart d ↔
        G.Reachable C.sourceDart d := by
    rw [C.loopGraph_setOpen_eq_twoEdgeSwitch omega e]
    exact medialTwoEdgeSwitch_reachable_iff_of_disjoint G hwestSouth
      heastNorth hsourceWest hsourceEast
  intro side hopen
  have hopenReach := (C.mem_exploration_iff _ _).1 hopen
  have hclosed : (e, side) ∈ C.exploration (setClosed e.1 omega) :=
    (C.mem_exploration_iff _ _).2 ((hiff (e, side)).1 hopenReach)
  cases side
  · exact hwest hclosed
  · exact heast hclosed
  · exact hwest ((C.closed_west_mem_iff_south omega e).2 hclosed)
  · exact heast ((C.closed_east_mem_iff_north omega e).2 hclosed)


theorem local_switch_membership_classification
    (omega : ConfigSpace (Sym2 P.V)) (e : FKIsingMedialVertex P) :
    ((e, .west) ∉ C.exploration (setClosed e.1 omega) ∧
        (e, .east) ∉ C.exploration (setClosed e.1 omega) ∧
        forall side, (e, side) ∉ C.exploration (setOpen e.1 omega)) ∨
      ((e, .west) ∈ C.exploration (setClosed e.1 omega) ∧
        (e, .east) ∉ C.exploration (setClosed e.1 omega) ∧
        forall side, (e, side) ∈ C.exploration (setOpen e.1 omega)) ∨
      ((e, .west) ∉ C.exploration (setClosed e.1 omega) ∧
        (e, .east) ∈ C.exploration (setClosed e.1 omega) ∧
        forall side, (e, side) ∈ C.exploration (setOpen e.1 omega)) ∨
      ((e, .west) ∈ C.exploration (setClosed e.1 omega) ∧
        (e, .east) ∈ C.exploration (setClosed e.1 omega)) := by
  classical
  by_cases hwest : (e, .west) ∈ C.exploration (setClosed e.1 omega)
  · by_cases heast : (e, .east) ∈ C.exploration (setClosed e.1 omega)
    · exact Or.inr (Or.inr (Or.inr ⟨hwest, heast⟩))
    · exact Or.inr (Or.inl ⟨hwest, heast,
        C.open_local_mem_of_closed_west_mem_not_east omega e hwest heast⟩)
  · by_cases heast : (e, .east) ∈ C.exploration (setClosed e.1 omega)
    · exact Or.inr (Or.inr (Or.inl ⟨hwest, heast,
        C.open_local_mem_of_closed_east_mem_not_west omega e heast hwest⟩))
    · exact Or.inl ⟨hwest, heast,
        C.open_local_not_mem_of_closed_west_east_not_mem omega e hwest heast⟩


end FKIsingDobrushinMedialComplex
end
end StatMech.Universality
