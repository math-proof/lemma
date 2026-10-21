import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothDegreeBoundOver_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R] [CommSemiring S]
  (f : R →+* S) {P : MvPolynomial (Fin m) R} {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBoundOver P r) :
-- imply
  rothDegreeBoundOver (MvPolynomial.map f P) r := by
-- proof
  intro k hk h
  apply hP k (MvPolynomial.support_map_subset f P hk)


-- created on 2026-10-21
