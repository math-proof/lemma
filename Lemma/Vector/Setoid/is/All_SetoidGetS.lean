import sympy.Basic
import sympy.vector.functions


@[main, comm, mp, mpr]
private lemma main
  [Setoid α]
-- given
  (a b : List.Vector α n) :
-- imply
  a ≈ b ↔ ∀ i : Fin n, a[i] ≈ b[i] := by
-- proof
  aesop


@[main, comm, mp, mpr]
private lemma fin
  [Setoid α]
-- given
  (a b : List.Vector α n) :
-- imply
  a ≈ b ↔ ∀ i : Fin n, a.get i ≈ b.get i := by
-- proof
  aesop


-- created on 2025-12-23
