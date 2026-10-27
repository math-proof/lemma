import Theorem.Logic.SEq
import Def.Data.Holor.Defs.Part4


@[path]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B) :
-- imply
  A.data ≃ B.data := by
-- proof
  simp [SEq] at h ⊢
  aesop


-- created on 2025-05-29
