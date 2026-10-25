/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InsideCoveringClose
import Theorem.StatisticalMechanics.Code.Ising.PeierlsPlanarAssembly
open Set SimpleGraph Function


set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice


variable {W : Type*} {G : SimpleGraph W}


theorem paa_reach_a_or_b {a b : W} {s x : W} (p : G.Walk s x)
    (h : (G.deleteEdges {s(a, b)}).Reachable a s ∨ (G.deleteEdges {s(a, b)}).Reachable b s) :
    ((G.deleteEdges {s(a, b)}).Reachable a x ∨ (G.deleteEdges {s(a, b)}).Reachable b x) := by
  classical
  induction p with
  | nil => exact h
  | @cons u v w huv q ih =>
    apply ih
    by_cases hed : s(u, v) = s(a, b)
    · rw [Sym2.eq_iff] at hed
      rcases hed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right; exact Reachable.refl _
      · left; exact Reachable.refl _
    · have hadj1 : (G.deleteEdges {s(a, b)}).Adj u v := by
        rw [deleteEdges_adj]; exact ⟨huv, by simpa using hed⟩
      rcases h with hu | hu
      · left; exact hu.trans hadj1.reachable
      · right; exact hu.trans hadj1.reachable


theorem paa_sup_edge_deleteEdges_eq {a b : W} (hnotin : s(a, b) ∉ G.edgeSet) :
    (G ⊔ edge a b).deleteEdges {s(a, b)} = G := by
  ext x y
  simp only [deleteEdges_adj, sup_adj, edge_adj, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h | ⟨hc, _⟩, hne2⟩
    · exact h
    · exact absurd (by rw [Sym2.eq_iff]; tauto) hne2
  · intro hxy
    refine ⟨Or.inl hxy, ?_⟩
    intro hc
    rw [Sym2.eq_iff] at hc
    apply hnotin
    rw [SimpleGraph.mem_edgeSet]
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy
    · exact hxy.symm


theorem paa_two_components_count_sup {a b : W}
    (hnotin : s(a, b) ∉ G.edgeSet)
    (hconn : (G ⊔ edge a b).Connected)
    (hbridge : ¬ G.Reachable a b) :
    Nat.card G.ConnectedComponent = 2 := by
  classical
  have hGeq : G = (G ⊔ edge a b).deleteEdges {s(a, b)} := (paa_sup_edge_deleteEdges_eq hnotin).symm
  set G₁ := (G ⊔ edge a b).deleteEdges {s(a, b)} with hG1
  have hbridge' : ¬ G₁.Reachable a b := by rw [← hGeq]; exact hbridge
  let f : G₁.ConnectedComponent → Bool :=
    ConnectedComponent.lift (fun v => decide (G₁.Reachable a v)) (by
      intro u v p _
      have hreach : G₁.Reachable u v := ⟨p⟩
      simp only [decide_eq_decide]
      exact ⟨fun h => h.trans hreach, fun h => h.trans hreach.symm⟩)
  have hf_mk : ∀ v : W, f (G₁.connectedComponentMk v) = decide (G₁.Reachable a v) := fun _ => rfl
  have hevery : ∀ x : W, G₁.Reachable a x ∨ G₁.Reachable b x := by
    intro x
    obtain ⟨p⟩ := hconn.preconnected a x
    exact paa_reach_a_or_b p (Or.inl (Reachable.refl a))
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · refine ConnectedComponent.ind₂ ?_
      intro u v huv
      rw [hf_mk, hf_mk, decide_eq_decide] at huv
      rw [ConnectedComponent.eq]
      by_cases hau : G₁.Reachable a u
      · exact hau.symm.trans (huv.mp hau)
      · have hav : ¬ G₁.Reachable a v := fun h => hau (huv.mpr h)
        have hbu : G₁.Reachable b u := (hevery u).resolve_left hau
        have hbv : G₁.Reachable b v := (hevery v).resolve_left hav
        exact hbu.symm.trans hbv
    · intro c
      cases c with
      | true => exact ⟨G₁.connectedComponentMk a, by rw [hf_mk]; simp⟩
      | false => exact ⟨G₁.connectedComponentMk b, by rw [hf_mk]; simp [hbridge']⟩
  rw [hGeq, Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_bool]


end Ising
end StatMech
