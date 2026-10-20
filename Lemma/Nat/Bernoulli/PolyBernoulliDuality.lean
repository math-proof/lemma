import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.PolyBernoulliDuality
open scoped BigOperators
open MetaMathlibExt


/--
[arakawa_kaneko_duality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliDuality.lean)
-/
@[path]
private lemma arakawa_kaneko_duality_eq
  {n k : ℕ} :
-- imply
  polyBernoulli n (-(k : ℤ)) = polyBernoulli k (-(n : ℤ)) := by
-- proof
  apply MetaMathlibExt.arakawa_kaneko_duality n k


-- created on 2026-10-20
