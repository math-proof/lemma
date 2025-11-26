import Lemma.Tensor.EqStackSUFnGet.of.Eq
import Lemma.Tensor.Select.eq.Stack_Select.of.GtLength
open Tensor


@[main]
private lemma main
  {d : ℕ}
-- given
  (h_n : n = m)
  (h_d : s.length > d)
  (X : Tensor α (n :: s))
  (i : Fin s[d]) :
-- imply
  have : X.length = m := by aesop
  X.select ⟨d + 1, by grind⟩ ⟨i, by grind⟩ ≃ [k < m] (X[k].select ⟨d, by simpa⟩ ⟨i, by simp⟩) := by
-- proof
  simp only [Select.eq.Stack_Select.of.GtLength h_d X i]
  apply EqStackSUFnGet.of.Eq h_n (fun s => s.eraseIdx d) (fun X => X.select ⟨d, by simpa⟩ ⟨i, by simp⟩)


-- created on 2025-11-15
