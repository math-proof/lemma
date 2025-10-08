import Lemma.Algebra.Le_Sub_1.of.Lt
import Lemma.Nat.LtVal
open Algebra Nat


@[main]
private lemma main
-- given
  (i : Fin n) :
-- imply
  i ≤ n - 1 := by
-- proof
  have := LtVal i
  apply Le_Sub_1.of.Lt this


-- created on 2025-05-07
-- updated on 2025-06-07
