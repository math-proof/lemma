import Lemma.Finset.Any_In.is.Ne_Empty
open Finset


@[main]
private lemma main
-- given
  (i : Fin n) :
-- imply
  (Finset.univ : Finset (Fin n)) ≠ ∅ := by
-- proof
  apply Ne_Empty.of.Any_In
  use i
  aesop


-- created on 2025-11-06
