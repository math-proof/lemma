import Lemma.Tensor.GetGetSlice.eq.Get.of.Lt_Min
open Tensor


@[main]
private lemma main
  {X : Tensor α s}
  {n : ℕ}
-- given
  (i : Fin ((⟨0, n, 1⟩ : Slice).length X.length))
  (h : i.val < n ⊓ X.length) :
-- imply
  have : i < X.length := by aesop
  X[:n][i] = X[i] := by
-- proof
  match s with
  | [] =>
    simp [Tensor.length] at h
  | s₀ :: s =>
    simp only [Tensor.length] at h
    apply GetGetSlice.eq.Get.of.Lt_Min X h


@[main]
private lemma fin
  {X : Tensor α s}
  {n : ℕ}
-- given
  (i : Fin ((⟨0, n, 1⟩ : Slice).length X.length))
  (h : i.val < n ⊓ X.length) :
-- imply
  have h_i : i < X.length := by aesop
  X[:n].get i = X.get ⟨i, h_i⟩ := by
-- proof
  apply main
  assumption


-- created on 2025-08-05
