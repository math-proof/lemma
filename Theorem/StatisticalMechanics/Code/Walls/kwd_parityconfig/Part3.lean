/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.kwd_parityconfig.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Walls

section Disagree

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


variable {G}

omit [DecidableEq V] in


theorem mem_disagree_iff (c : V → Bool) {x y : V} (h : G.Adj x y) :
    s(x, y) ∈ disagree G c ↔ c x ≠ c y := by
  unfold disagree
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, h2⟩; exact of_decide_eq_true h2
  · intro hne
    exact ⟨by rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact h,
      decide_eq_true hne⟩

omit [DecidableEq V] in

theorem disagree_subset_edgeFinset (c : V → Bool) : disagree G c ⊆ G.edgeFinset :=
  Finset.filter_subset _ _

end Disagree


section Handshake

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


theorem walkPar_disagree_eq_xor (c : V → Bool) {x y : V} (p : G.Walk x y) :
    walkPar G (disagree G c) p = (c x).xor (c y) := by
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
    rw [walkPar_cons, ih]
    have hdecne : ∀ a b : Bool, decide (a ≠ b) = a.xor b := by
      intro a b; cases a <;> cases b <;> simp
    have hedge : decide (s(u, v) ∈ disagree G c) = (c u).xor (c v) := by
      rw [decide_eq_decide.mpr (mem_disagree_iff c h), hdecne]
    rw [hedge]
    
    set a := c u; set b := c v; set d := c w
    cases a <;> cases b <;> cases d <;> rfl


theorem disagree_evenOnAllCycles (c : V → Bool) :
    EvenOnAllCycles G (disagree G c) := by
  intro x p
  rw [walkPar_disagree_eq_xor c p]
  cases c x <;> rfl

end Handshake
end StatMech.Walls
