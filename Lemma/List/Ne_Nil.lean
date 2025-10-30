import Lemma.Nat.LtVal
import Lemma.List.Ne_Nil.is.GtLength_0
open Nat List


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  s ≠ [] := by
-- proof
  have h_i := LtVal i
  apply Ne_Nil.of.GtLength_0
  omega


-- created on 2025-10-10
