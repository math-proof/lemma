import Lemma.List.GetPermute.eq.Ite.of.GtLength.GtLength
import Theorem.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Drop.eq.Nil.of.LeLength
open List Nat


@[path]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {j : ℕ}
-- given
  (h : i > j)
  (d : ℕ) :
-- imply
  (s.permute i d)[j]'(by simp; omega) = s[j] := by
-- proof
  if h_d : i + d < s.length then
    rw [GetPermute.eq.Ite.of.GtLength.GtLength h_d (by omega)]
    split_ifs
    repeat rfl
  else
    simp at h_d
    have h_d : i + d ≥ s.length - 1 := by omega
    have h_eq : s.permute i d = s.permute i (s.length - 1 - i : ℕ) := by
      repeat rw [Permute.eq.Append_AppendRotateTakeDrop]
      simp_all [show (s.length - 1 - i + 1) = s.length - i by omega]
      rw [Drop.eq.Nil.of.LeLength (i := i + (d + 1)) (by have := Nat.succ_le_succ h_d; omega)]
      simp
      omega
    simp [h_eq]
    rw [GetPermute.eq.Ite.of.GtLength.GtLength (by omega) (by omega)]
    split_ifs
    repeat rfl


-- created on 2025-11-02
