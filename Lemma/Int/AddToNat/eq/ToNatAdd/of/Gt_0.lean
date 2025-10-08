import Lemma.Int.AddToNat.eq.ToNatAdd.of.Ge_0
import Lemma.Algebra.Ge.of.Gt
open Algebra Int


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n > 0)
  (m : ℕ) :
-- imply
  n.toNat + m = (n + m).toNat := by
-- proof
  apply AddToNat.eq.ToNatAdd.of.Ge_0
  apply Ge.of.Gt h


-- created on 2025-07-14
