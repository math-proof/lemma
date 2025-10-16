import Lemma.Nat.NotGe.is.Lt
open Nat


@[main, comm, mp]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  (¬a ≤ b) ↔ (a > b) :=
-- proof
  ⟨Lt.of.NotGe, NotGe.of.Lt⟩


-- created on 2025-03-21
