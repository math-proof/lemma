import sympy.vector.vector
import Lemma.Vector.Eq.of.Eq_Cast.Eq
open Vector


@[main]
private lemma main
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h_n : n = m)
  (h : ∀ i : Fin n, a[i] = b[i]) :
-- imply
  a ≃ b := by
-- proof
  apply Eq.of.Eq_Cast.Eq h_n.symm
  aesop


@[main]
private lemma fin
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h_n : n = m)
  (h : ∀ i : Fin n, a.get i = b.get ⟨i, by omega⟩) :
-- imply
  a ≃ b :=
-- proof
  main h_n h


-- created on 2025-07-11
