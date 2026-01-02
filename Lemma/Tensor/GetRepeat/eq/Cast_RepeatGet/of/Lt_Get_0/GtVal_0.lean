import Lemma.Nat.LtSubS.of.Lt.Le
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.LengthRepeat.eq.Get_0.of.GtVal_0
import Lemma.Bool.EqCast.of.SEq
import Lemma.List.TailSet.eq.SetTail.of.Gt_0
import Lemma.Nat.EqAddSub.of.Ge
open Tensor List Bool Nat


@[main, fin]
private lemma main
  {d : Fin s.length}
-- given
  (h : d.val > 0)
  (h_i : i < s[0])
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  have : i < (X.repeat n d).length := by simpa [LengthRepeat.eq.Get_0.of.GtVal_0 h]
  have : d - 1 < s.tail.length := by
    simp
    apply LtSubS.of.Lt.Le (by linarith) (by simp)
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  have h_cast : s.tail.set (d - 1) (n * s.tail[(⟨d - 1, by assumption⟩ : Fin s.tail.length)]) = (s.set d (n * s[(d : Fin s.length)])).tail := by
    simp [SetTail.eq.TailSet.of.Gt_0 h]
    simp [EqAddSub.of.Ge (Ge_1.of.Gt_0 h)]
  (X.repeat n d)[i] = cast (by rw [h_cast]) (X[i].repeat n ⟨d - 1, by assumption⟩) := by
-- proof
  intro h_i' h_d' h_i' h_cast
  let i : Fin s[0] := ⟨i, h_i⟩
  have := GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0 h h_i X n
  simp at this
  apply Eq_Cast.of.SEq this


-- created on 2025-07-09
-- updated on 2025-07-10
