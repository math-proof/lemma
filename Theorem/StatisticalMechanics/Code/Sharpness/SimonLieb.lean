/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpnessFull.Part2
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

section FirstExit

variable {V : Type*} {G : SimpleGraph V}


theorem walk_firstExit {o z : V} (w : G.Walk o z) (S : Finset V) (ho : o ∈ S) (hz : z ∉ S)
    [DecidablePred (fun i => w.getVert i ∉ S)] :
    ∃ k, 1 ≤ k ∧ k ≤ w.length ∧
      w.getVert k ∉ S ∧ w.getVert (k - 1) ∈ S ∧
      G.Adj (w.getVert (k - 1)) (w.getVert k) ∧
      (∀ j < k, w.getVert j ∈ S) := by
  classical
  
  have hlen : w.getVert w.length ∉ S := by rw [w.getVert_length]; exact hz
  have hex : ∃ i, w.getVert i ∉ S := ⟨w.length, hlen⟩
  
  have hspec : w.getVert (Nat.find hex) ∉ S := Nat.find_spec hex
  
  have hkpos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · exact absurd (by rw [h0, w.getVert_zero]; exact ho) hspec
    · exact h0
  
  have hkle : Nat.find hex ≤ w.length := Nat.find_le hlen
  
  have hprev : ∀ j < Nat.find hex, w.getVert j ∈ S :=
    fun j hj => not_not.mp (Nat.find_min hex hj)
  
  have hadj : G.Adj (w.getVert (Nat.find hex - 1)) (w.getVert (Nat.find hex)) := by
    have heq : (Nat.find hex - 1) + 1 = Nat.find hex := by omega
    have h := w.adj_getVert_succ (i := Nat.find hex - 1) (by omega)
    rwa [heq] at h
  exact ⟨Nat.find hex, hkpos, hkle, hspec, hprev (Nat.find hex - 1) (by omega), hadj, hprev⟩

end FirstExit


section BackboneFirstExit

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem backbone_getVert_odd {n : Current V} {a b : V} (p : IsBackbonePath G n a b)
    {i : ℕ} (hi : i < p.1.length) :
    G.Adj (p.1.getVert i) (p.1.getVert (i + 1)) ∧
      Odd (n s(p.1.getVert i, p.1.getVert (i + 1))) := by
  have hadj := p.1.adj_getVert_succ hi
  rw [oddSubgraph_adj] at hadj
  exact hadj


theorem backbone_firstExit {n : Current V} {o z : V} (p : IsBackbonePath G n o z)
    (S : Finset V) (ho : o ∈ S) (hz : z ∉ S) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ p.1.length ∧
      p.1.getVert (k - 1) ∈ S ∧ p.1.getVert k ∉ S ∧
      s(p.1.getVert (k - 1), p.1.getVert k) ∈ G.edgeFinset ∧
      Odd (n s(p.1.getVert (k - 1), p.1.getVert k)) ∧
      1 ≤ n s(p.1.getVert (k - 1), p.1.getVert k) ∧
      (∀ j < k, p.1.getVert j ∈ S) := by
  classical
  obtain ⟨k, hk1, hkle, hyk, hxk, hadj, hprev⟩ :=
    walk_firstExit (G := oddSubgraph G n) p.1 S ho hz
  have heq : (k - 1) + 1 = k := by omega
  
  have hmem : s(p.1.getVert (k - 1), p.1.getVert k) ∈ G.edgeFinset := by
    have hadjG : G.Adj (p.1.getVert (k - 1)) (p.1.getVert k) := oddSubgraph_le G n hadj
    rw [mem_edgeFinset, mem_edgeSet]; exact hadjG
  
  have hodd : Odd (n s(p.1.getVert (k - 1), p.1.getVert k)) := by
    have h := (backbone_getVert_odd G p (i := k - 1) (by omega)).2
    rwa [heq] at h
  exact ⟨k, hk1, hkle, hxk, hyk, hmem, hodd, hodd.pos, hprev⟩


theorem backbone_firstExit_crossing {n : Current V} {o z : V} (p : IsBackbonePath G n o z)
    (S : Finset V) (ho : o ∈ S) (hz : z ∉ S) :
    ∃ x y : V, x ∈ S ∧ y ∉ S ∧ s(x, y) ∈ G.edgeFinset ∧ 1 ≤ n s(x, y) := by
  obtain ⟨k, _, _, hx, hy, he, _, hpos, _⟩ := backbone_firstExit G p S ho hz
  exact ⟨p.1.getVert (k - 1), p.1.getVert k, hx, hy, he, hpos⟩

end BackboneFirstExit
end Sharpness
end StatMech
