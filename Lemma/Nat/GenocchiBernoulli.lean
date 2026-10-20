import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GenocchiBernoulli
open MetaMathlibExt


/--
[genocchiNumber_eq_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GenocchiBernoulli.lean)
-/
@[path]
private lemma genocchiNumber_eq_bernoulli_eq
  {n : ℕ} :
-- imply
  genocchiNumber n = 2 * (1 - (2 : ℚ) ^ n) * bernoulli n := by
-- proof
  apply MetaMathlibExt.genocchiNumber_eq_bernoulli n

/--
[genocchiNumberViaBernoulli_eq_genocchiNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GenocchiBernoulli.lean)
-/
@[path]
private lemma genocchiNumberViaBernoulli_eq_genocchiNumber_eq
  {n : ℕ} :
-- imply
  genocchiNumberViaBernoulli n = genocchiNumber n := by
-- proof
  apply MetaMathlibExt.genocchiNumberViaBernoulli_eq_genocchiNumber n


-- created on 2026-10-20
