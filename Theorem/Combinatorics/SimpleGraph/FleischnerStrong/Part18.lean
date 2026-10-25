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
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part30
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

theorem cutSplit_forward_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (r : ℕ) (hr : r ≤ cut.1.val) :
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Reachable
      (c.getVert r) x := by
  let selected : ℕ → Prop := fun t ↦
    ∃ ht : t < c.length, t < cut.1.val ∧ q.copies ⟨t, ht⟩ = 1
  have hterminal : ¬selected cut.1.val := by
    rintro ⟨hlen, hlt, hcopy⟩
    omega
  have hadj : ∀ i, i < cut.1.val → ¬selected (i + 1) →
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 1)) := by
    intro i hicut hnsel
    let j : Fin c.length := ⟨i, lt_trans hicut cut.1.isLt⟩
    have hjcut : j ≠ cut.1 := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [j] at hval
      omega
    apply c.cutSplit_compressed_adj_original hc cover q cut hlast j hjcut
    intro a
    apply split_partner_ne_forward_original q cut.1 j hlast hicut
    intro hinext
    by_contra hzero
    have hone : q.copies ⟨j.val + 1, lt_trans hinext cut.1.isLt⟩ = 1 := by
      have hlt := q.copies_lt_two ⟨j.val + 1, lt_trans hinext cut.1.isLt⟩
      omega
    apply hnsel
    exact ⟨lt_trans hinext cut.1.isLt, hinext, hone⟩
  have hskip : ∀ i, i + 2 ≤ cut.1.val → selected (i + 1) →
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 2)) := by
    rintro i hi2 ⟨hi1len, hi1cut, hcopy⟩
    let a : ActiveCycleCopy q := ⟨⟨i + 1, hi1len⟩, hcopy⟩
    have hane : a.1 ≠ cut.1 := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [a] at hval
      omega
    let a' : UncutActiveCycleCopy q cut := ⟨a, hane⟩
    have h := c.cutSplit_compressed_adj_forward_skip hc cover q cut hlast a' hi1cut
    change (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
      (c.getVert ((i + 1) - 1)) (c.getVert ((i + 1) + 1)) at h
    convert h using 1
    all_goals congr 1
  have hpath := reachable_of_adj_or_skip
    (G := (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying)
    (fun i ↦ c.getVert i) cut.1.val selected hterminal hadj hskip
  have hroot := hpath 0 (Nat.zero_le cut.1.val)
  exact (hpath r hr).trans (by simpa using hroot.symm)

theorem cut_split_partner_ne_reverse_original {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (cut : ActiveCycleCopy q)
    (j : Fin n) (hlast : q.copies (cycleLastIndex n) = 0)
    (hcutj : cut.1.val < j.val)
    (hzero : cut.1.val + 1 < j.val → q.copies ⟨j.val - 1, by omega⟩ = 0)
    (i : UncutActiveCycleCopy q cut) :
    splitPartnerIndex cut.1 i.1.1 ≠ j := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [splitPartnerIndex_val_on_active q cut.1 hlast i.1] at hval
  have hipos : 0 < i.1.1.val :=
    Nat.pos_of_ne_zero (fun h ↦ i.1.ne_zero q (Fin.ext h))
  by_cases hik : i.1.1.val < cut.1.val
  · simp [hik] at hval
    omega
  · simp [hik] at hval
    by_cases hjnext : j.val = cut.1.val + 1
    · apply i.2
      apply Fin.ext
      omega
    · have hcutj' : cut.1.val + 1 < j.val := by omega
      have hiprev : i.1.1 = ⟨j.val - 1, by omega⟩ := by
        apply Fin.ext
        change i.1.1.val = j.val - 1
        omega
      have hone := i.1.2
      rw [hiprev, hzero hcutj'] at hone
      omega

theorem cutSplit_reverse_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (r : ℕ) (hcutr : cut.1.val + 1 ≤ r) (hrn : r < c.length) :
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Reachable
      (c.getVert r) x := by
  let m := c.length - (cut.1.val + 1)
  let selected : ℕ → Prop := fun t ↦
    ∃ i : UncutActiveCycleCopy q cut,
      ¬i.1.1.val < cut.1.val ∧ i.1.1.val + t + 1 = c.length
  have hterminal : ¬selected m := by
    rintro ⟨i, hik, hi⟩
    have hval : i.1.1.val = cut.1.val := by
      dsimp [m] at hi
      omega
    exact i.2 (Fin.ext hval)
  have hadj : ∀ a, a < m → ¬selected (a + 1) →
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
        (c.getVert (c.length - a)) (c.getVert (c.length - (a + 1))) := by
    intro a ham hnsel
    let j : Fin c.length := ⟨c.length - a - 1, by
      have hn := NeZero.pos c.length
      dsimp [m] at ham
      omega⟩
    have hcutj : cut.1.val < j.val := by
      dsimp [j, m] at ham ⊢
      omega
    have hjcut : j ≠ cut.1 := fun h ↦ by
      have hval := congrArg Fin.val h
      omega
    have hnotpaired : ∀ i : UncutActiveCycleCopy q cut,
        splitPartnerIndex cut.1 i.1.1 ≠ j := by
      intro i
      apply cut_split_partner_ne_reverse_original q cut j hlast hcutj
      intro hcutj'
      by_contra hzero
      have hone : q.copies ⟨j.val - 1, by omega⟩ = 1 := by
        have hlt := q.copies_lt_two ⟨j.val - 1, by omega⟩
        omega
      let i' : ActiveCycleCopy q := ⟨⟨j.val - 1, by omega⟩, hone⟩
      have hine : i'.1 ≠ cut.1 := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp [i'] at hval
        omega
      apply hnsel
      refine ⟨⟨i', hine⟩, ?_, ?_⟩
      · dsimp [i']
        omega
      · change (j.val - 1) + (a + 1) + 1 = c.length
        have hjval : j.val = c.length - a - 1 := rfl
        omega
    have horig :=
      c.cutSplit_compressed_adj_original hc cover q cut hlast j hjcut hnotpaired
    have hsucc : c.getVert (j + 1) = c.getVert (c.length - a) := by
      congr 1
      dsimp [j, m] at ham ⊢
      omega
    rw [hsucc] at horig
    exact horig.symm
  have hskip : ∀ a, a + 2 ≤ m → selected (a + 1) →
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
        (c.getVert (c.length - a)) (c.getVert (c.length - (a + 2))) := by
    rintro a ha2 ⟨i, hik, hi⟩
    have h := c.cutSplit_compressed_adj_reverse_skip hc cover q cut hlast i hik
    dsimp [m] at ha2
    convert h using 1 <;> congr 1 <;> omega
  have hpath := reachable_of_adj_or_skip
    (G := (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying)
    (fun t ↦ c.getVert (c.length - t)) m selected hterminal hadj hskip
  have ht : c.length - r ≤ m := by
    dsimp [m]
    omega
  have hroot := hpath 0 (Nat.zero_le m)
  have hrpath := hpath (c.length - r) ht
  simpa [m, Nat.sub_sub_self (Nat.le_of_lt hrn)] using hrpath.trans hroot.symm

end Walk
end SimpleGraph
