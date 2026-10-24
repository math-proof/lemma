import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PellLucasSequence
open MetaMathlibExt


namespace MetaMathlibExt

/--
[pellLucasSequence_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PellLucasSequence.lean)
-/
@[path]
lemma pellLucasSequence_succ_succ
  {n : ℕ} :
-- imply
  pellLucasSequence (n + 2) =
      2 * pellLucasSequence (n + 1) + pellLucasSequence n :=
-- proof
  rfl

end MetaMathlibExt

/--
[pellLucasSequence_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PellLucasSequence.lean)
-/
@[path]
private lemma pellLucasSequence_zero_eq
  :
-- imply
  pellLucasSequence 0 = 1 := by
-- proof
  apply MetaMathlibExt.pellLucasSequence_zero

/--
[pellLucasSequence_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PellLucasSequence.lean)
-/
@[path]
private lemma pellLucasSequence_one_eq
  :
-- imply
  pellLucasSequence 1 = 1 := by
-- proof
  apply MetaMathlibExt.pellLucasSequence_one


-- created on 2026-10-20
-- updated on 2026-10-23
