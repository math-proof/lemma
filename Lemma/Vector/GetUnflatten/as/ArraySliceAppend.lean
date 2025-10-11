import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Bool.EqCast.of.Eq
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Vector.Unflatten.eq.AppendUnflattenS.of.SEq_Append
import Lemma.Vector.GetAppend.eq.Get
import Lemma.Vector.SEqArraySliceS.of.SEq.Eq.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEq.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Vector.GetUnflatten.as.ArraySlice.of.Lt
import Lemma.Nat.LtVal
open Algebra Vector Bool Nat


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
      apply SEqArraySliceS.of.SEq.Eq.Eq rfl rfl ∘ SEq_Cast.of.SEq.Eq (by assumption) ∘ SEq.of.Eq
      rfl
    ·
      apply GetUnflatten.as.ArraySlice.of.Lt


-- created on 2025-07-15
