module

public import Mathlib
public import Theorem.Fin.GetRothFlip.eq.Sub.of.RothBox

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothCentered_flip_same](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothCentered_RothFlip.eq.NegRothCentered.of.RothBox.All_Gt_0
  {m : ℕ}
  {r : Fin m → ℕ}
-- given
  (hr : ∀ h, 0 < r h)
  (h : Fin m)
  (j : RothBox r) :
-- imply
  rothCentered r (rothFlip r h j) h = -rothCentered r j h := by
-- proof
  unfold rothCentered
  rw [GetRothFlip.eq.Sub.of.RothBox]
  have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
  rw [Nat.cast_sub hjle]
  have hrR : (0 : ℝ) < r h := by exact_mod_cast hr h
  field_simp
  ring


-- created on 2026-10-21
