import Lemma.Algebra.NotGe.is.Lt
open Algebra


@[main, comm, mp]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  (¬a ≤ b) ↔ (a > b) :=
-- proof
  ⟨Lt.of.NotGe, NotGe.of.Lt⟩


-- created on 2025-03-21
