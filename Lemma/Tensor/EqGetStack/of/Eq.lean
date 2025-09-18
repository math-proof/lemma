import Lemma.Tensor.EqGetStack
open Tensor


@[main]
private lemma main
-- given
  (h : n = m)
  (f : ℕ → Tensor α s)
  (i : Fin m) :
-- imply
  have : i < n := by simp_all
  ([i < n] f i)[i] = f i := by
-- proof
  let j : Fin n := ⟨i, by simp_all⟩
  have := EqGetStack f j
  simp at this
  have h_j : j = i.val := rfl
  simp [j] at this
  simp_all


-- created on 2025-05-23
-- updated on 2025-06-30
