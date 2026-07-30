import sympy.tensor.tensor
import Lemma.Tensor.SelectResize.as.Select_Mod_Get.of.Lt.GtLength
open Tensor


@[main]
private lemma main
  [Zero α]
  {d : Fin s.length}
  (i : Fin s[d])
  {n : ℕ}
  (X : Tensor α s) :
-- imply
  (X.resize d (s[d] ⊔ n)).select ⟨d, by simp⟩ ⟨i, by simp⟩ ≃ X.select d i := by
-- proof
  apply SelectResize.as.Select_Mod_Get.of.Lt.GtLength _ i.isLt



-- created on 2026-07-30
