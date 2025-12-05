import Lemma.Nat.LeAddS.is.Le
import sympy.sets.sets
open Nat


@[main, comm, mp, mpr]
private lemma main
  [Preorder α]
  [Add α]
  [AddRightMono α] [AddRightReflectLE α]
-- given
  (a b c x : α) :
-- imply
  x ∈ Icc a b ↔ x + c ∈ Icc (a + c) (b + c) := by
-- proof
  constructor
  <;> intros h
  <;> let ⟨h_ge, h_le⟩ := h
  <;> constructor
  repeat apply LeAddS.of.Le; assumption
  repeat apply Le.of.LeAddS; assumption


-- created on 2025-12-05
