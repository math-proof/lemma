import Lemma.Tensor.SEqGetS.of.SEq.Lt_Length
import Lemma.Tensor.Lt_Length.of.GtLength_0
import Lemma.Tensor.SEqBFnS.of.SEq
import Lemma.Bool.SEq.is.Eq
open Tensor Bool


@[main]
private lemma main
  {X : Tensor α s}
  {X' : Tensor α s'}
-- given
  (h : s.length > 0)
  (h_X : X ≃ X')
  (i : Fin s[0])
  (g : List ℕ → List ℕ)
  (f : (s : List ℕ) → Tensor α s → Tensor α (g s)) :
-- imply
  have h_s := h_X.left
  have := Lt_Length.of.GtLength_0 h X i
  have := Lt_Length.of.GtLength_0 (by grind) X' ⟨i, by grind⟩
  f s.tail X[i] ≃ f s'.tail X'[i] := by
-- proof
  intro _ h_i _
  apply SEqBFnS.of.SEq
  apply SEqGetS.of.SEq.Lt_Length h_i h_X


-- created on 2025-07-13
