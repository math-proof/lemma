import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PellLucasSequence
open MetaMathlibExt


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

/--
[pellLucasSequence_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PellLucasSequence.lean)
-/
@[path]
private lemma pellLucasSequence_succ_succ_eq
  {n : ℕ} :
-- imply
  pellLucasSequence (n + 2) =
      2 * pellLucasSequence (n + 1) + pellLucasSequence n := by
-- proof
  apply MetaMathlibExt.pellLucasSequence_succ_succ n


-- created on 2026-10-20
