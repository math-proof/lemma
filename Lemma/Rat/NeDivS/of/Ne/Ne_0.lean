import Lemma.Nat.EqMulS.of.Eq
import Lemma.Rat.EqMulDiv.of.Ne_0
open Nat Rat


@[main]
private lemma main
  [GroupWithZero α]
  {x y d : α}
-- given
  (h : x ≠ y)
  (h_d : d ≠ 0) :
-- imply
  x / d ≠ y / d := by
-- proof
  contrapose! h
  have h := EqMulS.of.Eq h d
  repeat rw [EqMulDiv.of.Ne_0 h_d] at h
  assumption


-- created on 2025-10-01
