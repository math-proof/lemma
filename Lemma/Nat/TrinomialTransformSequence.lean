import Mathlib
import sympy.Basic
import Def.NumberTheory.TrinomialTransformSequence
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[trinomialTransformSequence_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TrinomialTransformSequence.lean)
-/
@[path]
lemma trinomialTransformSequence_zero
  [Semiring R]
  {a : ℕ → R} :
-- imply
  trinomialTransformSequence a 0 = a 0 := by
-- proof
  simp [trinomialTransformSequence, trinomialCoefficient, Polynomial.coeff_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[trinomialTransformSequence_zero_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TrinomialTransformSequence.lean)
-/
@[path]
lemma trinomialTransformSequence_zero_apply
  [Semiring R]
  {n : ℕ} :
-- imply
  trinomialTransformSequence (fun _ => (0 : R)) n = 0 := by
-- proof
  simp [trinomialTransformSequence]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
