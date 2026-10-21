import Mathlib
import Lemma.Fin.GetRothFlip.eq.Sub.of.RothBox
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothCentered_flip_same](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
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
