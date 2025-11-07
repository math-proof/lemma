import Lemma.Tensor.EqGetStack
open Tensor


@[main]
private lemma main
-- given
  (h : i < n)
  (f : Fin n → Tensor α s) :
-- imply
  ([i < n] f i)[i] = f ⟨i, h⟩ := by
-- proof
  let j : Fin n := ⟨i, by simp_all⟩
  have := EqGetStack.fn f j
  simp at this
  have h_j : j = i := rfl
  simp [j] at this
  simp_all


@[main]
private lemma fin
-- given
  (h : i < n)
  (f : Fin n → Tensor α s) :
-- imply
  ([i < n] f i).get ⟨i, by simpa⟩ = f ⟨i, h⟩ := by
-- proof
  apply main h


-- created on 2025-06-30
