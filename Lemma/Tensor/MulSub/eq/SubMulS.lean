import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataSub.eq.SubDataS
import Theorem.Tensor.Eq.is.EqDataS
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.MulSub.eq.SubMulS |
| comm | Tensor.SubMulS.eq.MulSub |
-/
@[path, comm]
private lemma main
  [NonUnitalNonAssocRing α]
-- given
  (A B : Tensor α s)
  (x : α) :
-- imply
  (A - B) * x = A * x - B * x := by
-- proof
  apply Eq.of.EqDataS
  rw [DataMul.eq.MulData]
  repeat rw [DataSub.eq.SubDataS]
  repeat rw [DataMul.eq.MulData]
  ext i
  have get_sub (U V : List.Vector α s.prod) : (U - V).get i = U.get i - V.get i := by
    rw [_root_.sub_eq_add_neg U V, GetAdd.eq.AddGetS.fin, GetNeg.eq.NegGet.fin]
    apply (_root_.sub_eq_add_neg _ _).symm
  simp only [HMul.hMul, List.Vector.get_map, get_sub]
  apply sub_mul


-- created on 2025-12-29
-- updated on 2026-11-20
