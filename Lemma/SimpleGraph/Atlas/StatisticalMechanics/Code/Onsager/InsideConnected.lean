import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.InsideConnected
open StatMech StatMech.Onsager StatMech.Onsager.InsideConnected


/--
[lexmax_corner_cell_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InsideConnected.lean)
-/
@[path]
private lemma lexmax_corner_cell_inside_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  ∃ M : Fin n, d (M - 1) = 1 ∧ d M = 2 ∧ rayParity d ((pos d M).1 - 1) ((pos d M).2 - 1) = 1 := by
-- proof
  apply StatMech.Onsager.InsideConnected.lexmax_corner_cell_inside d hclosed hsimple hreflexfree


-- created on 2026-10-23
