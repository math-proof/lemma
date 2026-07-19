import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.Tensor.GetBmm.as.BmmGetS.of.Eq
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthBmm.eq.Length
open List Tensor


@[main, fin, cast, cast.fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : bz.length > 0)
  (X : Tensor α (bz ++ [m, k]))
  (Y : Tensor α (bz ++ [k, n]))
  (i : Fin bz[0]) :
-- imply
  have h_bz : bz = bz[0] :: bz.tail := (EqCons_Tail.of.GtLength_0 h).symm
  have h_X : bz ++ [m, k] = (bz[0] :: bz.tail) ++ [m, k] := by
    simpa using congrArg (· ++ [m, k]) h_bz
  have h_Y : bz ++ [k, n] = (bz[0] :: bz.tail) ++ [k, n] := by
    simpa using congrArg (· ++ [k, n]) h_bz
  let X' := cast (congrArg (Tensor α) h_X) X
  let Y' := cast (congrArg (Tensor α) h_Y) Y
  have h_i : i < (X.bmm Y).length := by
    rw [LengthBmm.eq.Length]
    rw [Length.eq.Get_0.of.GtLength_0 (by simp)]
    grind
  (X.bmm Y)[i]'h_i ≃ X'[i].bmm Y'[i] := by
-- proof
  intros h_bz h_X h_Y X' Y' h_i
  exact GetBmm.as.BmmGetS.of.Eq h_bz X Y i


-- created on 2026-07-19
