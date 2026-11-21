import Def.Data.Tensor.Repeat
import Instance.Data.Tensor.Defs.Part2
import Lemma.Tensor.Eq.is.EqDataS
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.Repeat.eq.Zero |
| subst 0 | Tensor.Repeat.eq.Zero.of.Eq_0 |
-/
@[path, subst 0]
private lemma main
  [Zero α]
-- given
  (X : Tensor α s)
  (d : Fin s.length) :
-- imply
  X.repeat d 0 = 0 := by
-- proof
  have h_prod : (s.set d (0 * s[d])).prod = 0 := by
    simpa only [Nat.zero_mul, Nat.mul_zero] using
      List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength d.isLt 0
  have h_empty (Y : Tensor α (s.set d (0 * s[d]))) : Y.data.val = [] :=
    List.length_eq_zero_iff.mp (Y.data.property.trans h_prod)
  apply Eq.of.EqDataS
  apply Subtype.ext
  simp only [h_empty]


-- created on 2026-07-12
-- updated on 2026-11-20
