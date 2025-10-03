import sympy.tensor.tensor
import Lemma.Algebra.EqMin_SubMulS
import Lemma.Algebra.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Logic.HEq.of.SEq
import Lemma.Vector.GetSplitAt_1.as.ArraySlice.of.Lt_Get_0.GtLength_0
open Algebra Logic Vector


@[main]
private lemma main
-- given
  (a : Tensor α (s₀ :: s))
  (i : Fin s₀) :
-- imply
  a.toVector[i].data.val = (a.data.array_slice (i * s.prod) s.prod).val := by
-- proof
  simp [Tensor.toVector]
  congr
  ·
    funext a
    rw [EqMin_SubMulS]
  ·
    congr
    have := GetCast_Map.eq.UFnGet.of.Eq.Lt (n := ((s₀ :: s).take 1).prod) (n' := (s₀ :: s).headD 1) (i := i)
      (by simp)
      (by simp)
      (List.Vector.splitAt a.data 1)
      (fun data ↦ (⟨data⟩ : Tensor α s))
    simp at this
    rw [this]
    apply HEq.of.SEq
    apply GetSplitAt_1.as.ArraySlice.of.Lt_Get_0.GtLength_0
    repeat simp


-- created on 2025-05-18
-- updated on 2025-07-17
