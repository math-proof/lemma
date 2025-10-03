import Lemma.Algebra.AddMul.lt.Mul.of.Lt.Lt
import Lemma.List.TailSet_0.eq.Tail
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Algebra.MulMul.eq.Mul_Mul
open Algebra List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (h_j : j < n)
  (h_k : k < (s.set 0 (n * s[0])).tail.prod) :
-- imply
  (j * s[0] + i) * s.tail.prod + k < n * s.prod := by
-- proof
  have h_add_mul := AddMul.lt.Mul.of.Lt.Lt h_j h_i
  have := AddMul.lt.Mul.of.Lt.Lt h_add_mul h_k
  rw [MulMul.eq.Mul_Mul] at this
  rw [TailSet_0.eq.Tail] at this
  convert this
  apply Prod.eq.Mul_ProdTail.of.GtLength_0 h_s


-- created on 2025-07-18
