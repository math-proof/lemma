import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.ResidueClassPsi
open Chebyshev


/--
[psiResidueClass_of_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ResidueClassPsi.lean)
-/
@[path]
private lemma psiResidueClass_of_lt_one_eq
  {q : ℕ}
  {a : ZMod q}
  {x : ℝ}
-- given
  (hx : x < 1) :
-- imply
  psiResidueClass a x = 0 := by
-- proof
  apply Chebyshev.psiResidueClass_of_lt_one a hx


-- created on 2026-10-20
