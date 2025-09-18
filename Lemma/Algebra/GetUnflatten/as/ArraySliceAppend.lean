import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Logic.EqCast.of.Eq
import Lemma.Logic.SEq.of.SEq.SEq
import Lemma.Algebra.Unflatten.eq.AppendUnflattenS.of.SEq_Append
import Lemma.Algebra.GetAppend.eq.Get
import Lemma.Algebra.EqArraySliceS.of.Eq.Eq.Eq
import Lemma.Logic.EqCast.of.SEq.Eq
import Lemma.Logic.SEq.of.Eq
import Lemma.Logic.SEqCast.of.Eq
import Lemma.Algebra.GetUnflatten.as.ArraySlice.of.Lt
open Algebra Logic


@[main]
private lemma main
-- given
  (a : List.Vector α (m * k))
  (b : List.Vector α (n * k))
  (i : Fin m) :
-- imply
  a.unflatten[i] ≃ (a ++ b).array_slice (i * k) k := by
-- proof
  have h_prod := AddMulS.eq.MulAdd m n k
  let ab : List.Vector α ((m + n) * k) := cast (by simp_all) (a ++ b)
  have h_ab : ab ≃ a ++ b := by
    simp [ab]
    apply SEqCast.of.Eq h_prod
  apply SEq.of.SEq.SEq (c := ab.unflatten[i])
  ·
    rw [Unflatten.eq.AppendUnflattenS.of.SEq_Append h_ab]
    rw [GetAppend.eq.Get]
  ·
    apply SEq.of.SEq.SEq (c := ab.array_slice (i * k) k)
    ·
      apply EqArraySliceS.of.Eq.Eq.Eq rfl rfl
      apply Eq_Cast.of.SEq.Eq (by assumption)
      apply SEq.of.Eq rfl
    ·
      have := LtVal i
      apply GetUnflatten.as.ArraySlice.of.Lt (by linarith)


-- created on 2025-07-15
