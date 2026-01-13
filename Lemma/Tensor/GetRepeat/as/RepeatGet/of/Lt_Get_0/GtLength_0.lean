import Lemma.Nat.LtAdd.of.Lt_Sub
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthRepeat.eq.Get_0.of.GtVal_0
open Nat Tensor


@[main, fin]
private lemma main
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (X : Tensor α s)
  (n : ℕ)
  (d : Fin s.tail.length) :
-- imply
  have h_d := d.isLt
  have : i < (X.repeat n ⟨d + 1, by apply LtAdd.of.Lt_Sub; simp_all⟩).length := by
    rwa [LengthRepeat.eq.Get_0.of.GtVal_0]
    simp
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.repeat n ⟨d + 1, by grind⟩)[i] ≃ X[i].repeat n d := by
-- proof
  have := GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0 (by grind) h_i X n (d := ⟨d + 1, by grind⟩)
  simp_all


-- created on 2026-01-13
