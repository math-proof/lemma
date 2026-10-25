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
import Def.Combinatorics.BellWeakExcedance.Part3


section

namespace MetaMathlibExt

theorem removeBlock_parts {n : ℕ} {S B : Finset (Fin n)}
    (P : Finpartition S) (hBmem : B ∈ P.parts) :
    (removeBlock P hBmem).parts = P.parts.erase B := rfl

theorem addBlock_parts {n : ℕ} {S B : Finset (Fin n)}
    (hBsub : B ⊆ S) (hBne : B.Nonempty) (Q : Finpartition (S \ B)) :
    (addBlock hBsub hBne Q).parts = insert B Q.parts := rfl

theorem addBlock_part {n : ℕ} {S B : Finset (Fin n)}
    (hBsub : B ⊆ S) (hBne : B.Nonempty) (Q : Finpartition (S \ B))
    (m0 : Fin n) (hmB : m0 ∈ B) :
    (addBlock hBsub hBne Q).part m0 = B := by
  have hmS : m0 ∈ S := hBsub hmB
  have hmem : B ∈ (addBlock hBsub hBne Q).parts := by
    rw [addBlock_parts]
    exact Finset.mem_insert_self B Q.parts
  exact (addBlock hBsub hBne Q).part_eq_of_mem hmem hmB

theorem block_notMem_parts {n : ℕ} {S B : Finset (Fin n)}
    (m0 : Fin n) (hmB : m0 ∈ B) (Q : Finpartition (S \ B)) :
    B ∉ Q.parts := by
  intro h
  have hsub : B ⊆ S \ B := Q.subset h
  have hmem : m0 ∈ S \ B := hsub hmB
  rw [Finset.mem_sdiff] at hmem
  exact hmem.2 hmB

theorem finpartition_eq_of_parts_eq {α : Type*} [Lattice α] [OrderBot α]
    {a : α} {P Q : Finpartition a} (h : P.parts = Q.parts) : P = Q := by
  obtain ⟨p1, s1, u1, b1⟩ := P
  obtain ⟨p2, s2, u2, b2⟩ := Q
  simp only at h
  subst h
  rfl

theorem add_remove_cancel {n : ℕ} {S B : Finset (Fin n)}
    (P : Finpartition S) (hBmem : B ∈ P.parts)
    (hBsub : B ⊆ S) (hBne : B.Nonempty) :
    addBlock hBsub hBne (removeBlock P hBmem) = P := by
  apply finpartition_eq_of_parts_eq
  rw [addBlock_parts, removeBlock_parts]
  exact Finset.insert_erase hBmem

theorem remove_add_cancel {n : ℕ} {S B : Finset (Fin n)}
    (hBsub : B ⊆ S) (hBne : B.Nonempty) (Q : Finpartition (S \ B))
    (m0 : Fin n) (hmB : m0 ∈ B) :
    removeBlock (addBlock hBsub hBne Q)
      (by rw [addBlock_parts]; exact Finset.mem_insert_self B Q.parts) = Q := by
  apply finpartition_eq_of_parts_eq
  rw [removeBlock_parts, addBlock_parts]
  have hnot : B ∉ Q.parts := block_notMem_parts m0 hmB Q
  exact Finset.erase_insert hnot

end MetaMathlibExt
end
