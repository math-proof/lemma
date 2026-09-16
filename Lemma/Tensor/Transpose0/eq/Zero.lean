import torch.Tensor.permute
import Lemma.Tensor.EqCast_0'0.of.Eq
import Lemma.Tensor.Permute0.eq.Zero
open Tensor


@[main]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (i j : ℕ) :
-- imply
  (0 : Tensor α s).transpose i j = 0 := by
-- proof
  simp (config := { zeta := true }) only [Tensor.transpose]
  split_ifs
  · rw [Tensor.EqCast_0'0.of.Eq (by rw [‹i = j›]; simp [List.swap_self])]
  · rw [Tensor.EqCast_0'0.of.Eq (by obtain hi | hj := ‹_› <;> simp_all)]
  · -- else branch, i > j: the inner args if selects ⟨j, i⟩
    rw [Tensor.Permute0.eq.Zero, Tensor.Permute0.eq.Zero]
    rw [Tensor.EqCast_0'0.of.Eq (by
      let i' := (if i > j then (j, i) else (i, j)).1
      let j' := (if i > j then (j, i) else (i, j)).2
      have h_ite : (⟨i', j'⟩ : ℕ × ℕ) = if i > j then ⟨j, i⟩ else ⟨i, j⟩ := rfl
      rw [← List.Swap.eq.PermutePermute.of.Lt.GtLength
        (s := s) (i := i') (j := j')
        (by show s.length > (if i > j then (j, i) else (i, j)).2
            split_ifs; omega)
        (Nat.Lt.of.Prod.eq.IteGt.Ne ‹i ≠ j› h_ite)]
      exact List.Swap.of.Prod.eq.IteGt h_ite s)]
  · -- else branch, ¬ i > j (i.e. i < j): the inner args if selects ⟨i, j⟩
    rw [Tensor.Permute0.eq.Zero, Tensor.Permute0.eq.Zero]
    rw [Tensor.EqCast_0'0.of.Eq (by
      let i' := (if i > j then (j, i) else (i, j)).1
      let j' := (if i > j then (j, i) else (i, j)).2
      have h_ite : (⟨i', j'⟩ : ℕ × ℕ) = if i > j then ⟨j, i⟩ else ⟨i, j⟩ := rfl
      rw [← List.Swap.eq.PermutePermute.of.Lt.GtLength
        (s := s) (i := i') (j := j')
        (by show s.length > (if i > j then (j, i) else (i, j)).2
            split_ifs; omega)
        (Nat.Lt.of.Prod.eq.IteGt.Ne ‹i ≠ j› h_ite)]
      exact List.Swap.of.Prod.eq.IteGt h_ite s)]


-- created on 2026-09-16
