import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.EulerSeidelMatrix
open MetaMathlibExt


/--
[eulerSeidelMatrix_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerSeidelMatrix.lean)
-/
@[path]
private lemma eulerSeidelMatrix_eq_sum_eq
  [AddCommMonoid M]
  {a : ℕ → M}
  {n k : ℕ} :
-- imply
  eulerSeidelMatrix a n k = ∑ i ∈ Finset.range (k + 1), k.choose i • a (n + i) := by
-- proof
  apply MetaMathlibExt.eulerSeidelMatrix_eq_sum a n k


-- created on 2026-10-20
