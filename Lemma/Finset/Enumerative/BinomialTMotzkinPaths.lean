import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BinomialTMotzkinPaths
open scoped BigOperators
open MetaMathlibExt


/--
[binomial_tMotzkin_generatingFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomial_tMotzkin_generatingFunction_eq
  {t : ℕ}
-- given
  (ht : 1 ≤ t) :
-- imply
  let Step := by
-- proof
  apply MetaMathlibExt.binomial_tMotzkin_generatingFunction t ht


-- created on 2026-10-20
