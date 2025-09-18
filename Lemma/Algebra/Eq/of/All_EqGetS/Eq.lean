import stdlib.List.Vector
import Lemma.Algebra.Eq.of.Eq_Cast.Eq
open Algebra


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


-- created on 2025-07-11
