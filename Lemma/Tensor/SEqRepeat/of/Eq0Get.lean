import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Def.Data.Tensor.Repeat
import Def.Data.Tensor.Prod
import Lemma.List.EqProd_0.of.Eq0Get
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Tensor Vector Nat


@[path]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (h : s[d] = 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  X.repeat d n ≃ X := by
-- proof
  have h_set : s.set d (n * s[d]) = s := calc
    _ = s.set d s[d] := by rw [h, Nat.mul_zero]
    _ = s := List.set_getElem_self d.isLt
  unfold Tensor.repeat
  apply SEq.of.SEqDataS.Eq
  ·
    apply h_set
  ·
    have h_prod := EqProd_0.of.Eq0Get h
    have h_prod_eq_mul : (s.take ↑d).prod * (n * (s.drop ↑d).prod) = s.prod := by
      rw [← Nat.mul_assoc, Nat.mul_comm (s.take d).prod n, Nat.mul_assoc,
        ← List.prod_append, List.take_append_drop, h_prod, Nat.mul_zero]
    apply SEqCast.of.SEq.Eq
    ·
      rw [h_set]
      apply h_prod_eq_mul
    ·
      apply SEq.of.All_EqGetS.Eq.fin h_prod_eq_mul
      intro t
      have h_t := t.isLt
      omega


-- created on 2026-01-13
-- updated on 2026-11-20
