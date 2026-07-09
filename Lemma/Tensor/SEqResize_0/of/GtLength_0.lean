import Lemma.Bool.SEqCast.of.Eq
import Lemma.Tensor.Resize_0.eq.Ite.of.GtLength_0
open Bool Tensor


@[main, cast]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.resize ⟨0, by grind⟩ (s[0] ⊔ s[0]) ≃ X := by
-- proof
  rw [Resize_0.eq.Ite.of.GtLength_0 h]
  simp
  apply SEqCast.of.Eq
  simp


-- created on 2026-07-09
