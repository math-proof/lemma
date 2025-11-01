import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.DataGet.eq.GetUnflattenData
open Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have : i < X.length := by
    rw [Length.eq.Get_0.of.GtLength_0 h]
    simp
  have : i < (X.data.splitAt 1).length := by
    sorry
  X[i].data ≃ (X.data.splitAt 1)[i] := by
-- proof
  sorry


@[main]
private lemma fin
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have : i < X.length := by
    rw [Length.eq.Get_0.of.GtLength_0 h]
    simp
  have : i < (X.data.splitAt 1).length := by
    sorry
  (X.get ⟨i, by assumption⟩).data ≃ (X.data.splitAt 1).get ⟨i, by assumption⟩ := by
-- proof
  sorry


-- created on 2025-11-01
