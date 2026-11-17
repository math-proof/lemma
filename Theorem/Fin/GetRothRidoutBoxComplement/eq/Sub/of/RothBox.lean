module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothRidoutBoxComplement_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.GetRothRidoutBoxComplement.eq.Sub.of.RothBox
  {m : ℕ}
-- given
  (r : Fin m → ℕ)
  (j : RothBox r)
  (h : Fin m) :
-- imply
  ((rothRidoutBoxComplement r j) h : ℕ) = r h - j h := by
-- proof
  rfl


-- updated on 2026-11-13
-- created on 2026-10-21
