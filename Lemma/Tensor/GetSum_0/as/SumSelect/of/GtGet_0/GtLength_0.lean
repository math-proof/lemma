import Lemma.Tensor.LengthSum.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SelectSum.as.SumSelect.of.Lt
import Lemma.Tensor.Select_0.as.Get.of.GtGet_0.GtLength_0
open Tensor


@[main, comm]
private lemma main
  [AddCommMonoid α]
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (X : Tensor α (s₀ :: s)) :
-- imply
  have h_Xi : i < (X.sum 0).length := by rwa [LengthSum.eq.Get_0.of.GtLength_0 h_s]
  (X.sum 0).get ⟨i, h_Xi⟩ ≃ (X.select ⟨1, by grind⟩ ⟨i, by grind⟩).sum 0 := by
-- proof
  intro h_Xi
  apply SEq.trans (Get.as.Select_0.of.GtGet_0.GtLength_0 h_s h_i (X.sum 0))
  exact SelectSum.as.SumSelect.of.Lt (s := s₀ :: s) (d := ⟨1, Nat.succ_lt_succ h_s⟩) (k := 0) Nat.zero_lt_one X ⟨i, by simpa⟩


-- created on 2025-11-01
-- updated on 2026-08-27
