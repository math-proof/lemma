import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.PascalMatrix
open scoped BigOperators Topology
open MetaMathlibExt


/--
[pascalAlpha_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PascalMatrix.lean)
-/
@[path]
private lemma pascalAlpha_eq_eq
  {j : ℕ}
  {x : ℝ}
-- given
  (hx : |x| < 1) :
-- imply
  pascalAlpha j x = x ^ j / (1 - x) ^ (j + 1) := by
-- proof
  apply MetaMathlibExt.pascalAlpha_eq j x hx

/--
[tsum_pascalAlpha_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PascalMatrix.lean)
-/
@[path]
private lemma tsum_pascalAlpha_eq_eq
  {x : ℝ}
-- given
  (hx : |x| < 1 / 2) :
-- imply
  (∑' j, pascalAlpha j x) = (∑' j, ∑' i, (pascalEntry i j : ℝ) * x ^ i) ∧
    (∑' j, pascalAlpha j x) = ∑' j, x ^ j / (1 - x) ^ (j + 1) := by
-- proof
  apply MetaMathlibExt.tsum_pascalAlpha_eq x hx

/--
[tsum_pascalEntry_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PascalMatrix.lean)
-/
@[path]
private lemma tsum_pascalEntry_comm_eq
  {x : ℝ}
-- given
  (hx : |x| < 1 / 2) :
-- imply
  (∑' j, ∑' i, (pascalEntry i j : ℝ) * x ^ i) =
    (∑' i, ∑' j, (pascalEntry i j : ℝ) * x ^ i) ∧
    (∑' i, ∑' j, (pascalEntry i j : ℝ) * x ^ i) =
    (1 / (1 - x)) * (∑' j, (x / (1 - x)) ^ j) := by
-- proof
  apply MetaMathlibExt.tsum_pascalEntry_comm x hx

/--
[tsum_pascalEntry_row](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PascalMatrix.lean)
-/
@[path]
private lemma tsum_pascalEntry_row_eq
  {x : ℝ}
-- given
  (hx : |x| < 1 / 2) :
-- imply
  (∑' i, x ^ i * Finset.sum (Finset.range (i + 1))
    (fun j => (pascalEntry i j : ℝ))) = 1 / (1 - 2 * x) := by
-- proof
  apply MetaMathlibExt.tsum_pascalEntry_row x hx

/--
[tsum_pascalAlpha_eq_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PascalMatrix.lean)
-/
@[path]
private lemma tsum_pascalAlpha_eq_geometric_eq
  {x : ℝ}
-- given
  (hx : |x| < 1 / 2) :
-- imply
  (∑' j, pascalAlpha j x) = (∑' i, (2 * x) ^ i) ∧
    (∑' i, (2 * x) ^ i) = 1 / (1 - 2 * x) := by
-- proof
  apply MetaMathlibExt.tsum_pascalAlpha_eq_geometric x hx


-- created on 2026-10-20
