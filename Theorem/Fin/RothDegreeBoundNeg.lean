module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothDegreeBound_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothDegreeBoundNeg
  {m : ℕ} {P : MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBound P r) :
-- imply
  rothDegreeBound (-P) r := by
-- proof
  intro i hi h
  rw [MvPolynomial.support_neg] at hi
  apply hP i hi


-- updated on 2026-11-13
-- created on 2026-10-21
