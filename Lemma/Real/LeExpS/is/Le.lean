import Lemma.Nat.NotLt.is.Ge
import Lemma.Real.LtExpS.is.Lt
open Exp Nat


@[path, comm, mp, mpr]
private lemma main
  [ExpPos α]
-- given
  (a b : α) :
-- imply
  exp a ≤ exp b ↔ a ≤ b := by
-- proof
  simp only [Ge.is.NotLt]
  rw [not_iff_not]
  apply Real.LtExpS.is.Lt


-- created on 2025-12-27
