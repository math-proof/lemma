import Lemma.Tensor.SEqResize.of.GtLength_0
open Tensor


@[main, cast]
private lemma main
  [Zero α]
  {s : List ℕ}
  {i : Fin s.length}
-- given
  (h_n : n = s[i])
  (X : Tensor α s) :
-- imply
  X.resize ⟨i, by grind⟩ n ≃ X := by
-- proof
  have := SEqResize.of.GtLength_0 (by grind) X (i := i)
  grind


-- created on 2026-07-10
