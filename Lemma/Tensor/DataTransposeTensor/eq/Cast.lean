import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.SEqDataTransposeTensor
open Bool Tensor


@[main]
private lemma main
-- given
  (v : List.Vector α [n].prod) :
-- imply
  (⟨v⟩ : Tensor α [n, 1])ᵀ.data = cast (congrArg (List.Vector α) (by simp)) v := by
-- proof
  apply Eq_Cast.of.SEq
  apply SEqDataTransposeTensor


@[main]
private lemma row
-- given
  (v : List.Vector α [1, n].prod) :
-- imply
  (⟨v⟩ : Tensor α [1, n])ᵀ.data = cast (congrArg (List.Vector α) (by simp)) v := by
-- proof
  apply Eq_Cast.of.SEq
  apply SEqDataTransposeTensor.row


-- created on 2026-04-23
