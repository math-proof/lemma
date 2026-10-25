/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.TreeComplete

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


omit [Fintype E] [DecidableEq E] [DecidableEq V] in

theorem reachOpen_symm {endU endV : E → V} {ω : ConfigSpace E} {x y : V}
    (h : ReachOpen endU endV ω x y) : ReachOpen endU endV ω y x := by
  induction h with
  | refl x => exact ReachOpen.refl x
  | @step a b c e hopen hpair hrest ih =>
      have hstep : ReachOpen endU endV ω b a := by
        rcases hpair with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · exact ReachOpen.step e hopen (Or.inr ⟨hU, hV⟩) (ReachOpen.refl a)
        · exact ReachOpen.step e hopen (Or.inl ⟨hU, hV⟩) (ReachOpen.refl a)
      exact ih.trans hstep


omit [Fintype E] [DecidableEq E] in

theorem cb_adj_coord_le_one (d : ℕ) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) (i : Fin d) :
    (x i - y i).natAbs ≤ 1 := by
  simp only [hypercubicLattice_adj] at hadj
  calc (x i - y i).natAbs
      ≤ ∑ j : Fin d, (x j - y j).natAbs :=
        Finset.single_le_sum (f := fun j => (x j - y j).natAbs)
          (by intros; positivity) (Finset.mem_univ i)
    _ = 1 := hadj

omit [Fintype E] [DecidableEq E] in


theorem cb_mem_box_of_adj_box_pred (d k : ℕ) (hk : 1 ≤ k) (x y : Site d)
    (hx : x ∈ box d (k - 1)) (hadj : (hypercubicLattice d).Adj x y) : y ∈ box d k := by
  intro i
  have hdiff : (x i - y i).natAbs ≤ 1 := cb_adj_coord_le_one d x y hadj i
  have hxi : (x i).natAbs ≤ k - 1 := hx i
  have htri : (y i).natAbs ≤ (x i).natAbs + (x i - y i).natAbs := by
    have heq : y i = (y i - x i) + x i := by ring
    have hsym : (y i - x i).natAbs = (x i - y i).natAbs := by rw [← Int.natAbs_neg, neg_sub]
    calc (y i).natAbs = ((y i - x i) + x i).natAbs := by rw [← heq]
      _ ≤ (y i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _
      _ = (x i - y i).natAbs + (x i).natAbs := by rw [hsym]
      _ = (x i).natAbs + (x i - y i).natAbs := by ring
  omega

omit [Fintype E] [DecidableEq E] in


theorem reachOpen_crosses {d k : ℕ} (hk : 1 ≤ k) {endU endV : E → Site d}
    {ω : ConfigSpace E} (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    {o b : Site d} (h : ReachOpen endU endV ω o b)
    (ho : o ∈ box d (k - 1)) (hb : b ∉ box d (k - 1)) :
    ConnOpenSet endU endV ω o (vertexBoundary d k) := by
  induction h with
  | refl x => exact absurd ho hb
  | @step x y z e hopen hxy hrest ih =>
      have hadje : (hypercubicLattice d).Adj x y := by
        rcases hxy with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · rw [← hU, ← hV]; exact hadj e
        · rw [← hU, ← hV]; exact ((hypercubicLattice d).symm (hadj e))
      by_cases hyin : y ∈ box d (k - 1)
      · obtain ⟨w, hw, hreach⟩ := ih hyin hb
        exact ⟨w, hw, ReachOpen.step e hopen hxy hreach⟩
      · have hyboxk : y ∈ box d k := cb_mem_box_of_adj_box_pred d k hk x y ho hadje
        exact ⟨y, ⟨hyboxk, hyin⟩, ReachOpen.step e hopen hxy (ReachOpen.refl y)⟩

omit [Fintype E] [DecidableEq E] in


theorem connOpenSet_boundary_mono {d k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    {endU endV : E → Site d} {ω : ConfigSpace E}
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e)) {o : Site d}
    (ho : o ∈ box d (k - 1)) (h : ConnOpenSet endU endV ω o (vertexBoundary d n)) :
    ConnOpenSet endU endV ω o (vertexBoundary d k) := by
  obtain ⟨b, hbn, hreach⟩ := h
  
  have hbnotn1 : b ∉ box d (n - 1) := hbn.2
  have hsub : box d (k - 1) ⊆ box d (n - 1) := box_mono d (by omega)
  have hbnot : b ∉ box d (k - 1) := fun hc => hbnotn1 (hsub hc)
  exact reachOpen_crosses hk hadj hreach ho hbnot

omit [Fintype E] [DecidableEq E] in


theorem cb_not_mem_vertexBoundary {d k n : ℕ} (hkn : k ≤ n) {o : Site d}
    (ho : o ∈ box d (k - 1)) : o ∉ vertexBoundary d n := by
  intro hcon
  have : o ∈ box d (n - 1) := box_mono d (show k - 1 ≤ n - 1 by omega) ho
  exact hcon.2 this


end OSSS
end StatMech
