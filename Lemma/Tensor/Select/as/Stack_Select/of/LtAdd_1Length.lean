import Lemma.Nat.Lt_Sub.of.LtAdd
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Select.as.Stack_Select.of.Eq.GtLength
open Tensor Nat


@[main]
private lemma main
  {d : ℕ}
-- given
  (h : d + 1 < s.length)
  (X : Tensor α s)
  (i : Fin s[d + 1]) :
-- imply
  have h_length : s.length > 0 := by linarith
  have := Length.eq.Get_0.of.GtLength_0 h_length X
  X.select ⟨d + 1, by grind⟩ ⟨i, by simp⟩ ≃ [k < s[0]] (X[k].select ⟨d, by simp; omega⟩ ⟨i, by grind⟩) := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    apply Select.as.Stack_Select.of.Eq.GtLength rfl


-- created on 2025-11-15
