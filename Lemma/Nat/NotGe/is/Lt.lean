import Lemma.Nat.NotGe.of.Lt
import Lemma.Nat.Lt.is.Le.NotGe
open Nat


@[main, comm, mp]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  (¬a ≥ b) ↔ (a < b) := by
-- proof
  constructor <;>
    intro h
  ·
    apply Lt.of.Le.NotGe
    ·
      exact le_of_not_ge h
    ·
      exact h
  ·
    apply NotGe.of.Lt h


-- created on 2025-03-21
-- updated on 2025-08-02
