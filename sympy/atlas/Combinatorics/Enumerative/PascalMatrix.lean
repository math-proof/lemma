/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PascalMatrix.lean -/

import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The infinite Pascal matrix

Source: E. F. Cornelius Jr. and Phill Schultz, *Polynomial Points*:
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Schultz/schultz14.tex>.
-/

open scoped BigOperators Topology

namespace MetaMathlibExt

/-- Entry `(i, j)` of the infinite Pascal matrix. -/
def pascalEntry (i j : ℕ) : ℕ :=
  Nat.choose i j

/-- The column generating function `alpha_j(x) = ∑ i, choose i j * x ^ i`.

Concept `jis_sem_0dfae529bb25056055d54002`, statement
`jis_0e7580a02d8343e6906a8ac6`. -/
noncomputable def pascalAlpha (j : ℕ) (x : ℝ) : ℝ :=
  ∑' i, (pascalEntry i j : ℝ) * x ^ i
end MetaMathlibExt
