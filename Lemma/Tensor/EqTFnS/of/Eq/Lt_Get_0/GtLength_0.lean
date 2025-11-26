import Lemma.Tensor.EqLengthS.of.SEq
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.EqTFnS.of.Eq.GtLength
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (h : A ≃ B)
  (g : List ℕ → List ℕ)
  (f : (s : List ℕ) → (X : Tensor α s) → (i : Fin X.length) → Tensor α (g s)) :
-- imply
  have h_i : i < A.length := by rwa [Length.eq.Get_0.of.GtLength_0 h_s]
  f s A ⟨i, h_i⟩ ≃ f s' B ⟨i, by rwa [← EqLengthS.of.SEq h]⟩ := by
-- proof
  intro h_i
  apply EqTFnS.of.Eq.GtLength.tensor h_i h


-- created on 2025-07-13
