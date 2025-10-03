import sympy.tensor.tensor
import Lemma.Algebra.Lt_Add
import Lemma.Algebra.LtVal
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Logic.Eq.of.SEq
import Lemma.Logic.SEq.of.SEq.SEq
import Lemma.Vector.EqGetSUnflatten.of.Eq.Lt.Eq.Eq
import Lemma.Logic.EqCast.of.Eq
import Lemma.Vector.GetUnflatten.as.ArraySliceAppend
import Lemma.Vector.GetUnflatten.eq.Cast_ArraySlice.of.Lt
import Lemma.Logic.EqCast.of.SEq.Eq
import Lemma.Vector.EqArraySliceS.of.Eq
import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Algebra.Le_SubMulS.of.Lt
import Lemma.List.Prod.eq.Foldr
open Algebra Logic Vector List


@[main]
private lemma main
-- given
  (a : Tensor α (m :: s))
  (b : Tensor α (n :: s))
  (i : Fin m) :
-- imply
  have : i < m + n := by linarith [LtVal i]
  (a ++ b)[i] = a[i] := by
-- proof
  simp [GetElem.getElem]
  simp [Tensor.get]
  have h_lt := Lt_Add i n
  have hi := LtVal i
  simp [Tensor.length]
  simp [HAppend.hAppend]
  simp [Tensor.append]
  simp [Tensor.toVector]
  repeat rw [GetCast_Map.eq.UFnGet.of.Eq.Lt (by simp_all) (by simp)]
  unfold List.Vector.splitAt
  simp
  apply Eq.of.SEq.simp
  apply SEq.of.SEq.SEq (c := a.data.unflatten[i])
  ·
    apply SEq.of.SEq.SEq (c := (a.data ++ b.data).array_slice (i * s.prod) s.prod)
    ·
      rw [GetUnflatten.eq.Cast_ArraySlice.of.Lt (by linarith)]
      apply EqCast.of.SEq.Eq
      ·
        simp_all [Le_SubMulS.of.Lt h_lt]
      ·
        apply EqArraySliceS.of.Eq
        apply SEqCast.of.Eq
        simp [AddMulS.eq.MulAdd]
    ·
      apply GetUnflatten.as.ArraySliceAppend
  ·
    apply EqGetSUnflatten.of.Eq.Lt.Eq.Eq
    ·
      simp
    ·
      aesop
    ·
      apply SEqCast.of.Eq
      simp [Foldr.eq.Prod]


-- created on 2025-05-31
-- updated on 2025-07-15
