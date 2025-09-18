import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Tensor


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.repeat n ⟨0, h⟩).length = n * s[0] := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0] <;> 
    simp
  assumption


-- created on 2025-07-12
