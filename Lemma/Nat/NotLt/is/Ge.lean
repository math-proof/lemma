import Lemma.Nat.Ge.of.NotLt
import Lemma.Nat.NotLt.of.Ge
open Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  ¬a < b ↔ a ≥ b :=
-- proof
  ⟨Ge.of.NotLt, NotLt.of.Ge⟩


-- created on 2025-04-18
