import Lemma.Algebra.Eq_AddMulDiv___Mod
import Lemma.Algebra.LtDiv.of.Lt_Mul
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.Gt_0.of.GtMul
import Lemma.Nat.Mul
open Algebra Nat


@[main]
private lemma left
  {k n m : ℕ}
-- given
  (h : k < n * m) :
-- imply
  ∃ (i : Fin m) (j : Fin n), i * n + j = k := by
-- proof
  have hn := Gt_0.of.GtMul.left h
  have h_lt := LtMod.of.Gt_0 hn k
  use ⟨k / n, LtDiv.of.Lt_Mul.left h⟩, ⟨k % n, h_lt⟩
  simp
  apply Eq.symm
  apply Eq_AddMulDiv___Mod


@[main]
private lemma main
  {k n m : ℕ}
-- given
  (h : k < m * n) :
-- imply
  ∃ (i : Fin m) (j : Fin n), i * n + j = k := by
-- proof
  rw [Mul.comm] at h
  apply left h


-- created on 2025-05-29
