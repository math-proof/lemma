import Lemma.Finset.NeUnivEmpty
open Finset


@[main]
private lemma main
-- given
  (h : n > 0) :
-- imply
  (Finset.univ : Finset (Fin n)) ≠ ∅ :=
-- proof
  NeUnivEmpty ⟨0, h⟩


-- created on 2025-11-06
