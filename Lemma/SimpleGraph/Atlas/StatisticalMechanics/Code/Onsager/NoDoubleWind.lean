import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.NoDoubleWind
open StatMech StatMech.Onsager StatMech.Onsager.NoDoubleWind


/--
[pos_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind.lean)
-/
@[path]
private lemma pos_zero_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4} :
-- imply
  pos d 0 = 0 := by
-- proof
  apply StatMech.Onsager.NoDoubleWind.pos_zero d

/--
[pos_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind.lean)
-/
@[path]
private lemma pos_succ_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  pos d (k + 1) = pos d k + stepOf (d k) := by
-- proof
  apply StatMech.Onsager.NoDoubleWind.pos_succ d hclosed k

/--
[pos_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind.lean)
-/
@[path]
private lemma pos_pred_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {M : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  pos d M = pos d (M - 1) + stepOf (d (M - 1)) := by
-- proof
  apply StatMech.Onsager.NoDoubleWind.pos_pred d hclosed M

/--
[stepOf_coords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind.lean)
-/
@[path]
private lemma stepOf_coords_eq
  {n : ℕ}
  [NeZero n]
  {w : Fin 4} :
-- imply
  (w = 0 ∧ stepOf w = (1, 0)) ∨ (w = 1 ∧ stepOf w = (0, 1)) ∨ (w = 2 ∧ stepOf w = (-1, 0)) ∨ (w = 3 ∧ stepOf w = (0, -1)) := by
-- proof
  apply StatMech.Onsager.NoDoubleWind.stepOf_coords w

/--
[lexmax_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind.lean)
-/
@[path]
private lemma lexmax_corner_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  ∃ M : Fin n, d (M - 1) = 1 ∧ d M = 2 := by
-- proof
  apply StatMech.Onsager.NoDoubleWind.lexmax_corner d hclosed hreflexfree


-- created on 2026-10-23
