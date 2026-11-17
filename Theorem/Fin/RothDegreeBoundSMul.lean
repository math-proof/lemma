module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothDegreeBound_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothDegreeBoundSMul
  {m : ℕ} {P : MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBound P r)
  (c : ℤ) :
-- imply
  rothDegreeBound (c • P) r := by
-- proof
  intro i hi h
  apply hP i (MvPolynomial.support_smul hi)


-- updated on 2026-11-13
-- created on 2026-10-21
