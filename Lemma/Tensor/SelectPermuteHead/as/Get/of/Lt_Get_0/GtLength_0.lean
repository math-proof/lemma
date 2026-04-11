import Lemma.List.GetRotate.eq.Get_0.of.Gt_0.GtLength
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import stdlib.SEq
import sympy.tensor.tensor
open List Tensor Bool Fin Nat Vector


@[main]
private lemma main
  {s : List ℕ}
  {k : ℕ}
-- given
  (h_s : s.length > 1)
  (h_k : k < s[0])
  (X : Tensor α s) :
-- imply
  (X.permuteHead s.length).select ⟨s.length - 1, by grind⟩ ⟨k, by simp; rwa [GetRotate.eq.Get_0.of.Gt_0.GtLength (by grind) (by grind)]⟩ ≃ X.get ⟨k, by rwa [← Length.eq.Get_0.of.GtLength_0 (by omega) X] at h_k⟩ := by
-- proof
  sorry


-- created on 2026-04-09
-- updated on 2026-04-11
