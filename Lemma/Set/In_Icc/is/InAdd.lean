import Lemma.Nat.LeAddS.is.Le
import sympy.sets.sets
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Icc.is.InAdd |
| comm | Set.InAdd.is.In_Icc |
| mp 8 | Set.InAdd.of.In_Icc |
| mpr 4 | Set.In_Icc.of.InAdd |
-/
@[main, comm, mp 8, mpr 4]
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


-- created on 2020-02-27
-- updated on 2026-08-19
