import Lemma.Tensor.SEqResize_0.of.GtLength_0
open Tensor


@[main, cast]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_n : n = s[0])
  (X : Tensor α s) :
-- imply
  X.resize ⟨0, by grind⟩ n ≃ X := by
-- proof
  subst h_n
  apply SEqResize_0.of.GtLength_0


-- created on 2026-07-09
-- updated on 2026-07-10
