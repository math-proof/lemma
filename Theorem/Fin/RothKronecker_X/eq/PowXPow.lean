module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothKronecker_X](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothKronecker_X.eq.PowXPow
  {m : ℕ} [Field K]
  (D : ℕ) (h : Fin m) :
-- imply
  rothKronecker D (MvPolynomial.X h : MvPolynomial (Fin m) K) =
    Polynomial.X ^ D ^ (h : ℕ) := by
-- proof
  simp [rothKronecker]


-- updated on 2026-11-13
-- created on 2026-10-21
