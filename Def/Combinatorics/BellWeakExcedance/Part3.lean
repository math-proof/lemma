/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Bound
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Theorem.Combinatorics.BellWeakExcedance.Part2


section

namespace MetaMathlibExt

/-! ## Part A: Finpartitions are counted by Bell numbers -/

def removeBlock {n : ℕ} {S B : Finset (Fin n)} (P : Finpartition S)
    (hBmem : B ∈ P.parts) : Finpartition (S \ B) :=
  Finpartition.ofExistsUnique (P.parts.erase B)
    (by
      intro p hp
      rw [Finset.mem_erase] at hp
      have hdisj : Disjoint p B := by
        rw [Finset.disjoint_left]
        intro x hx hxB
        exact hp.1 (P.eq_of_mem_parts hp.2 hBmem hx hxB)
      exact Finset.subset_sdiff.mpr ⟨P.subset hp.2, hdisj⟩)
    (by
      intro a ha
      rw [Finset.mem_sdiff] at ha
      have haS : a ∈ S := ha.1
      have haB : a ∉ B := ha.2
      obtain ⟨t, ⟨ht, hat⟩, huniq⟩ := P.existsUnique_mem haS
      have htB : t ≠ B := by
        intro h
        rw [h] at hat
        exact haB hat
      refine ⟨t, ⟨Finset.mem_erase.mpr ⟨htB, ht⟩, hat⟩, ?_⟩
      intro y hy
      obtain ⟨hy_erase, hay⟩ := hy
      rw [Finset.mem_erase] at hy_erase
      exact huniq y ⟨hy_erase.2, hay⟩)
    (by
      intro h
      exact P.empty_notMem_parts (Finset.mem_of_mem_erase h))

def addBlock {n : ℕ} {S : Finset (Fin n)} {B : Finset (Fin n)}
    (hBsub : B ⊆ S) (hBne : B.Nonempty) (Q : Finpartition (S \ B)) :
    Finpartition S :=
  Finpartition.ofExistsUnique (insert B Q.parts)
    (by
      intro p hp
      rw [Finset.mem_insert] at hp
      rcases hp with rfl | hQ
      · exact hBsub
      · exact (Q.subset hQ).trans Finset.sdiff_subset)
    (by
      intro a haS
      by_cases haB : a ∈ B
      · refine ⟨B, ⟨Finset.mem_insert_self B Q.parts, haB⟩, ?_⟩
        intro y hy
        obtain ⟨hy_ins, hay⟩ := hy
        rw [Finset.mem_insert] at hy_ins
        rcases hy_ins with rfl | hQ
        · rfl
        · have hsub : y ⊆ S \ B := Q.subset hQ
          have hayS : a ∈ S \ B := hsub hay
          rw [Finset.mem_sdiff] at hayS
          exact absurd haB hayS.2
      · have haQ : a ∈ S \ B := Finset.mem_sdiff.mpr ⟨haS, haB⟩
        obtain ⟨t, ⟨ht, hat⟩, huniq⟩ := Q.existsUnique_mem haQ
        refine ⟨t, ⟨Finset.mem_insert_of_mem ht, hat⟩, ?_⟩
        intro y hy
        obtain ⟨hy_ins, hay⟩ := hy
        rw [Finset.mem_insert] at hy_ins
        rcases hy_ins with rfl | hQ
        · exact absurd hay haB
        · exact huniq y ⟨hQ, hay⟩)
    (by
      simp only [Finset.mem_insert, not_or]
      constructor
      · intro h
        rw [← h] at hBne
        exact Finset.not_nonempty_empty hBne
      · exact Q.empty_notMem_parts)

end MetaMathlibExt
end
