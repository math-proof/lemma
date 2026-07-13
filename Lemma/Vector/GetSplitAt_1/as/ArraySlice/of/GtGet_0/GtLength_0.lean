import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Le_SubMulS.of.Lt
import Lemma.Vector.SEqArraySliceS.of.SEq.Eq.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.Prod.eq.MulProdS
import Lemma.Vector.EqGetRange.of.Lt
open List Vector Bool Nat


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (v : List.Vector α s.prod) :
-- imply
  have : i < (s.take 1).prod := by rwa [ProdTake_1.eq.Get_0.of.GtLength_0 h_s]
  (v.splitAt 1)[i] ≃ v.array_slice (i * s.tail.prod) s.tail.prod := by
-- proof
  intro h_i
  unfold List.Vector.splitAt
  simp
  unfold List.Vector.unflatten
  simp
  apply SEqCast.of.SEq.Eq
  ·
    rw [EqMin.of.Le]
    apply Le_SubMulS.of.Lt
    simp
  ·
    apply SEqArraySliceS.of.SEq.Eq.Eq
    ·
      simp [EqGetRange.of.Lt]
    ·
      simp
    ·
      apply SEqCast.of.Eq
      apply Prod.eq.MulProdS


-- created on 2025-07-08
