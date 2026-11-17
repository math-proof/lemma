module

public import Mathlib
public import Def.NumberTheory.PrimeCounting.ResidueClassPsi

public section

open Chebyshev


namespace Chebyshev

/--
[psiResidueClass_of_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ResidueClassPsi.lean)
-/
public theorem psiResidueClass_of_lt_one
  {q : ℕ}
  {a : ZMod q}
  {x : ℝ}
-- given
  (hx : x < 1) :
-- imply
  psiResidueClass a x = 0 := by
-- proof
  simp [psiResidueClass, Nat.floor_eq_zero.mpr hx]

end Chebyshev


-- created on 2026-10-20
-- updated on 2026-10-26
