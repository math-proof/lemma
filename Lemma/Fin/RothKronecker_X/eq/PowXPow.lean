import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothKronecker_X](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [Field K]
  (D : ℕ) (h : Fin m) :
-- imply
  rothKronecker D (MvPolynomial.X h : MvPolynomial (Fin m) K) =
    Polynomial.X ^ D ^ (h : ℕ) := by
-- proof
  simp [rothKronecker]


-- created on 2026-10-21
