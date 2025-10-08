import Lemma.Algebra.Ge.of.NotLt
import Lemma.Algebra.GeMulS.of.Ge.Ge_0
import Lemma.Algebra.GeAddS.is.Ge
open Algebra


@[main]
private lemma main
  {i j m n : ℕ}
-- given
  (h : i * n + j < m * n) :
-- imply
  i < m := by
-- proof
  by_contra hi
  have hi := Ge.of.NotLt hi
  have hi := GeMulS.of.Ge.Ge_0 hi (show n ≥ 0 by simp)
  have hij := GeAddS.of.Ge j hi
  linarith


-- created on 2025-05-10
