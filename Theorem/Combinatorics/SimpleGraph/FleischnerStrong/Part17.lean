/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Def.Combinatorics.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.Contraction
import Lemma.SimpleGraph.EdgeIndexedMultigraph
import Lemma.SimpleGraph.Riha
import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
import Def.Combinatorics.SimpleGraph.Riha
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.ZMod.Basic
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part29
/-!
# The strengthened Fleischner theorem

This file proves the vertex-rooted form of Fleischner's theorem: the square has a Hamiltonian
cycle whose two edges at a prescribed vertex are edges of the original graph.

The proof-specific component, trail, transition, Euler-circuit, and marking constructions are
private to this module.
-/

/-! ## CycleComplement -/


namespace SimpleGraph

namespace Walk

theorem split_partner_ne_forward_original {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (k j : Fin n)
    (hlast : q.copies (cycleLastIndex n) = 0) (hjk : j.val < k.val)
    (hzero : ∀ h : j.val + 1 < k.val,
      q.copies ⟨j.val + 1, lt_trans h k.isLt⟩ = 0)
    (i : ActiveCycleCopy q) : splitPartnerIndex k i.1 ≠ j := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [splitPartnerIndex_val_on_active q k hlast i] at hval
  have hipos : 0 < i.1.val :=
    Nat.pos_of_ne_zero (fun h ↦ i.ne_zero q (Fin.ext h))
  by_cases hik : i.1.val < k.val
  · simp [hik] at hval
    have hjnext : j.val + 1 < k.val := by omega
    have hinext : i.1 = ⟨j.val + 1, lt_trans hjnext k.isLt⟩ := by
      apply Fin.ext
      change i.1.val = j.val + 1
      omega
    have hone := i.2
    rw [hinext, hzero hjnext] at hone
    omega
  · simp [hik] at hval
    omega

theorem split_partner_ne_reverse_original {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (k j : Fin n)
    (hlast : q.copies (cycleLastIndex n) = 0) (hkj : k.val ≤ j.val)
    (hzero : k.val < j.val →
      q.copies ⟨j.val - 1, by omega⟩ = 0)
    (i : ActiveCycleCopy q) : splitPartnerIndex k i.1 ≠ j := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [splitPartnerIndex_val_on_active q k hlast i] at hval
  have hipos : 0 < i.1.val :=
    Nat.pos_of_ne_zero (fun h ↦ i.ne_zero q (Fin.ext h))
  by_cases hik : i.1.val < k.val
  · simp [hik] at hval
    omega
  · simp [hik] at hval
    have hiend := i.val_add_one_lt q hlast
    by_cases hkj' : k.val = j.val
    · omega
    · have hkjlt : k.val < j.val := by omega
      have hiprev : i.1 = ⟨j.val - 1, by omega⟩ := by
        apply Fin.ext
        change i.1.val = j.val - 1
        omega
      have hone := i.2
      rw [hiprev, hzero hkjlt] at hone
      omega

theorem split_forward_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (r : ℕ) (hr : r ≤ k.val) :
    (c.splitCompressedMultigraph hc cover q k hlast).underlying.Reachable
      (c.getVert r) x := by
  let selected : ℕ → Prop := fun t ↦
    ∃ ht : t < c.length, t < k.val ∧ q.copies ⟨t, ht⟩ = 1
  have hterminal : ¬selected k.val := by
    rintro ⟨hklen, hkk, hcopy⟩
    omega
  have hadj : ∀ i, i < k.val → ¬selected (i + 1) →
      (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 1)) := by
    intro i hik hnsel
    let j : Fin c.length := ⟨i, lt_trans hik k.isLt⟩
    apply c.split_compressed_adj_original hc cover q k hlast j
    apply split_partner_ne_forward_original q k j hlast
    · exact hik
    · intro hinext
      have hcopy : q.copies
          ⟨j.val + 1, lt_trans hinext k.isLt⟩ = 0 := by
        by_contra hzero
        have hone : q.copies ⟨j.val + 1, lt_trans hinext k.isLt⟩ = 1 := by
          have hlt := q.copies_lt_two ⟨j.val + 1, lt_trans hinext k.isLt⟩
          omega
        apply hnsel
        exact ⟨lt_trans hinext k.isLt, hinext, hone⟩
      exact hcopy
  have hskip : ∀ i, i + 2 ≤ k.val → selected (i + 1) →
      (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 2)) := by
    rintro i hi2 ⟨hi1len, hi1k, hcopy⟩
    let a : ActiveCycleCopy q := ⟨⟨i + 1, hi1len⟩, hcopy⟩
    have h := c.split_compressed_adj_forward_skip hc cover q k hlast a hi1k
    simpa [a] using h
  have hpath := reachable_of_adj_or_skip
    (G := (c.splitCompressedMultigraph hc cover q k hlast).underlying)
    (fun i ↦ c.getVert i) k.val selected hterminal hadj hskip
  have hroot := hpath 0 (Nat.zero_le k.val)
  exact (hpath r hr).trans (by simpa using hroot.symm)

theorem split_reverse_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (r : ℕ) (hkr : k.val ≤ r) (hrn : r < c.length) :
    (c.splitCompressedMultigraph hc cover q k hlast).underlying.Reachable
      (c.getVert r) x := by
  let m := c.length - k.val
  let selected : ℕ → Prop := fun t ↦
    ∃ i : ActiveCycleCopy q, ¬i.1.val < k.val ∧ i.1.val + t + 1 = c.length
  have hterminal : ¬selected m := by
    rintro ⟨i, hik, hi⟩
    dsimp [m] at hi
    omega
  have hadj : ∀ a, a < m → ¬selected (a + 1) →
      (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
        (c.getVert (c.length - a)) (c.getVert (c.length - (a + 1))) := by
    intro a ham hnsel
    let j : Fin c.length := ⟨c.length - a - 1, by
      have hn := NeZero.pos c.length
      dsimp [m] at ham
      omega⟩
    have hkj : k.val ≤ j.val := by
      dsimp [j, m] at ham ⊢
      omega
    have hnotpaired : ∀ i : ActiveCycleCopy q, splitPartnerIndex k i.1 ≠ j := by
      apply split_partner_ne_reverse_original q k j hlast hkj
      intro hkjlt
      by_contra hzero
      have hone : q.copies ⟨j.val - 1, by omega⟩ = 1 := by
        have hlt := q.copies_lt_two ⟨j.val - 1, by omega⟩
        omega
      let i : ActiveCycleCopy q := ⟨⟨j.val - 1, by omega⟩, hone⟩
      apply hnsel
      refine ⟨i, ?_, ?_⟩
      · dsimp [i]
        omega
      · change (j.val - 1) + (a + 1) + 1 = c.length
        have hjval : j.val = c.length - a - 1 := rfl
        omega
    have horig := c.split_compressed_adj_original hc cover q k hlast j hnotpaired
    have hsucc : c.getVert (j + 1) = c.getVert (c.length - a) := by
      congr 1
      dsimp [j, m] at ham ⊢
      omega
    rw [hsucc] at horig
    exact horig.symm
  have hskip : ∀ a, a + 2 ≤ m → selected (a + 1) →
      (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
        (c.getVert (c.length - a)) (c.getVert (c.length - (a + 2))) := by
    rintro a ha2 ⟨i, hik, hi⟩
    have h := c.split_compressed_adj_reverse_skip hc cover q k hlast i hik
    dsimp [m] at ha2
    convert h using 1 <;> congr 1 <;> omega
  have hpath := reachable_of_adj_or_skip
    (G := (c.splitCompressedMultigraph hc cover q k hlast).underlying)
    (fun t ↦ c.getVert (c.length - t)) m selected hterminal hadj hskip
  have ht : c.length - r ≤ m := by
    dsimp [m]
    omega
  have hroot := hpath 0 (Nat.zero_le m)
  have hrpath := hpath (c.length - r) ht
  simpa [m, Nat.sub_sub_self (Nat.le_of_lt hrn)] using hrpath.trans hroot.symm

end Walk
end SimpleGraph
