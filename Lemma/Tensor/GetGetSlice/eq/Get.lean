import Lemma.Tensor.GetGetSlice.eq.Get.of.Lt_Min
open Tensor


@[main]
private lemma main
  {X : Tensor α s}
  {n : ℕ}
-- given
  (i : Fin ((⟨0, n, 1⟩ : Slice).length X.length)):
-- imply
  have : i < n ⊓ X.length := by simp [← List.LengthSlice.eq.Min]
  X[:n][i] = X[i]'(by aesop) := by
-- proof
  match s with
  | [] =>
    intro h
    simp [Tensor.length] at h
  | s₀ :: s =>
    intro h
    simp only [Tensor.length] at h
    apply GetGetSlice.eq.Get.of.Lt_Min X h


@[main]
private lemma fin
  {X : Tensor α s}
  {n : ℕ}
-- given
  (i : Fin ((⟨0, n, 1⟩ : Slice).length X.length)) :
-- imply
  have : i < n ⊓ X.length := by simp [← List.LengthSlice.eq.Min]
  X[:n].get i = X.get ⟨i, by aesop⟩ :=
-- proof
  main i


-- created on 2025-08-05
