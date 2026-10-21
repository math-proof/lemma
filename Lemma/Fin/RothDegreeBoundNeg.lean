import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothDegreeBound_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} {P : MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBound P r) :
-- imply
  rothDegreeBound (-P) r := by
-- proof
  intro i hi h
  rw [MvPolynomial.support_neg] at hi
  apply hP i hi


-- created on 2026-10-21
