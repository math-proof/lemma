module

public import Mathlib
public import Theorem.Fin.EqRothFlip.of.RothBox.Ne

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothCentered_flip_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothCentered_RothFlip.eq.RothCentered.of.RothBox.Ne
  {m : ℕ}
  {r : Fin m → ℕ}
  {h k : Fin m}
-- given
  (hhk : k ≠ h)
  (j : RothBox r) :
-- imply
  rothCentered r (rothFlip r h j) k = rothCentered r j k := by
-- proof
  simp only [rothCentered, EqRothFlip.of.RothBox.Ne hhk]


-- created on 2026-10-21
