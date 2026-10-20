import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.TrinomialTransformSequence
open scoped BigOperators
open MetaMathlibExt


/--
[trinomialTransformSequence_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TrinomialTransformSequence.lean)
-/
@[path]
private lemma trinomialTransformSequence_zero_eq
  [Semiring R]
  {a : ℕ → R} :
-- imply
  trinomialTransformSequence a 0 = a 0 := by
-- proof
  apply MetaMathlibExt.trinomialTransformSequence_zero a

/--
[trinomialTransformSequence_zero_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TrinomialTransformSequence.lean)
-/
@[path]
private lemma trinomialTransformSequence_zero_apply_eq
  [Semiring R]
  {n : ℕ} :
-- imply
  trinomialTransformSequence (fun _ => (0 : R)) n = 0 := by
-- proof
  apply MetaMathlibExt.trinomialTransformSequence_zero_apply n


-- created on 2026-10-20
