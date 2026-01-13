import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqProd_0.of.Eq0Get
import Lemma.List.EqSet.of.EqGet
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Tensor Vector Nat


@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (h : s[d] = 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  X.repeat n d ≃ X := by
-- proof
  unfold Tensor.repeat
  apply SEq.of.SEqDataS.Eq
  ·
    rw [h]
    apply EqSet.of.EqGet h
  ·
    have h_prod := EqProd_0.of.Eq0Get h
    have h_prod_eq_mul : (s.take ↑d).prod * (n * (s.drop ↑d).prod) = s.prod := by
      rw [h_prod]
      simp [Mul_Mul.eq.MulMul.comm]
      left
      grind
    apply SEqCast.of.SEq.Eq
    ·
      simp [h]
      rwa [EqSet.of.EqGet h]
    ·
      apply SEq.of.All_EqGetS.Eq.fin h_prod_eq_mul
      intro t
      have h_t := t.isLt
      omega


-- created on 2026-01-13
