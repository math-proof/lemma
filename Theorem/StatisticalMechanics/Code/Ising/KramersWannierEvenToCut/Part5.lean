/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Def.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part5
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section Reduction

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


section Additivity

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V} {δ₁ δ₂ : Finset (Sym2 V)}


theorem walkParity_union_disjoint (hdisj : Disjoint δ₁ δ₂) {x y : V} (p : Gp.Walk x y) :
    walkParity Gp (δ₁ ∪ δ₂) p = (walkParity Gp δ₁ p).xor (walkParity Gp δ₂ p) := by
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
    rw [walkParity_cons, walkParity_cons, walkParity_cons, ih]
    
    have hsplit : decide (s(u, v) ∈ δ₁ ∪ δ₂)
        = (decide (s(u, v) ∈ δ₁)).xor (decide (s(u, v) ∈ δ₂)) := by
      by_cases h1 : s(u, v) ∈ δ₁
      · have h2 : s(u, v) ∉ δ₂ := fun hc => (Finset.disjoint_left.mp hdisj h1) hc
        simp [Finset.mem_union, h1, h2]
      · by_cases h2 : s(u, v) ∈ δ₂ <;> simp [Finset.mem_union, h1, h2]
    rw [hsplit]
    
    cases decide (s(u, v) ∈ δ₁) <;> cases decide (s(u, v) ∈ δ₂) <;>
      cases walkParity Gp δ₁ q <;> cases walkParity Gp δ₂ q <;> rfl


theorem evenOnCycles_union_disjoint (hdisj : Disjoint δ₁ δ₂)
    (h1 : EvenOnCycles Gp δ₁) (h2 : EvenOnCycles Gp δ₂) :
    EvenOnCycles Gp (δ₁ ∪ δ₂) := by
  intro x p
  rw [walkParity_union_disjoint hdisj p, h1 x p, h2 x p]
  rfl


theorem walkParity_empty (Gp : SimpleGraph V) {x y : V} (p : Gp.Walk x y) :
    walkParity Gp (∅ : Finset (Sym2 V)) p = false := by
  induction p with
  | nil => rfl
  | cons h q ih => rw [walkParity_cons, ih]; simp


theorem evenOnCycles_empty (Gp : SimpleGraph V) : EvenOnCycles Gp (∅ : Finset (Sym2 V)) :=
  fun _ p => walkParity_empty Gp p

end Additivity


section Decomposition

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}


theorem evenOnCycles_biUnion {ι : Type*} (s : Finset ι)
    (pieces : ι → Finset (Sym2 V))
    (hdisj : (s : Set ι).PairwiseDisjoint pieces)
    (hpieces : ∀ i ∈ s, EvenOnCycles Gp (pieces i)) :
    EvenOnCycles Gp (s.biUnion pieces) := by
  classical
  induction s using Finset.induction with
  | empty =>
    have : (∅ : Finset ι).biUnion pieces = (∅ : Finset (Sym2 V)) := by simp
    rw [this]; exact evenOnCycles_empty Gp
  | @insert a s ha ih =>
    have hdisj_a : Disjoint (pieces a) (s.biUnion pieces) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdisj (Finset.mem_insert_self a s)
        (Finset.mem_insert_of_mem hi) (by rintro rfl; exact ha hi)
    have hrest : EvenOnCycles Gp (s.biUnion pieces) :=
      ih (hdisj.subset (by intro i hi; exact Finset.mem_insert_of_mem hi))
        (fun i hi => hpieces i (Finset.mem_insert_of_mem hi))
    have hunion : EvenOnCycles Gp (pieces a ∪ s.biUnion pieces) :=
      evenOnCycles_union_disjoint hdisj_a (hpieces a (Finset.mem_insert_self a s)) hrest
    rw [Finset.biUnion_insert]
    exact hunion

end Decomposition
end Reduction
end Ising
end StatMech
