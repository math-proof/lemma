module

public import Mathlib
public import Def.Combinatorics.Enumerative.QuadrinomialCoefficients

public section

open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[quadrinomialCoeff_eq_zhangVSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QuadrinomialCoefficients.lean)
-/
public theorem quadrinomialCoeff_eq_zhangVSum
  {n : ℕ} :
-- imply
  quadrinomialCoeff n = zhangVSum n 1 1 0 0 0 := by
-- proof
  simp [quadrinomialCoeff, zhangVSum]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
