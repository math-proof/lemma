import Lemma.List.LengthSlice.eq.Min
import Lemma.Tensor.GetGetSlice.eq.Get.of.Lt_Min
open Tensor List


@[main, fin]
private lemma main
  {X : Tensor α s}
  {n : ℕ}
-- given
  (i : Fin ((⟨0, n, 1⟩ : Slice).length X.length)) :
-- imply
  have : i < n ⊓ X.length := by simp [← LengthSlice.eq.Min]
  X[:n].get i = X[i]'(by aesop) := by
-- proof
  match s with
  | [] =>
    intro h
    simp [Tensor.length] at h
  | s₀ :: s =>
    intro h
    simp only [Tensor.length] at h
    apply GetGetSlice.eq.Get.of.Lt_Min X h


-- created on 2025-08-05
