import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.FaultFree3xnTiling
open MetaMathlibExt


/--
[isSquareOrDomino_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma isSquareOrDomino_iff_eq
  {n : ℕ}
  {d : Finset (TilingCell n)} :
-- imply
  IsSquareOrDomino d ↔
    (∃ x, d = {x}) ∨
    ∃ x y, x ≠ y ∧ TilingCell.Adjacent x y ∧ d = {x, y} := by
-- proof
  apply MetaMathlibExt.isSquareOrDomino_iff d

/--
[fault_free_3xn_tiling_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma fault_free_3xn_tiling_recursion_eq
  :
-- imply
  ∀ n : ℕ, 1 ≤ n → (verticalFaultFreeTilingCount n : ℤ) = tilingCount n := by
-- proof
  apply MetaMathlibExt.fault_free_3xn_tiling_recursion


-- created on 2026-10-20
