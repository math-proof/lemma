import Mathlib
import sympy.Basic
import sympy.AlgebraicGeometry.TangentSpace

open MvPolynomial

/--
[totalDerivativeAtLin_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/TangentSpace.lean)
-/
@[path]
private lemma totalDerivativeAtLin_apply_eq
  [Field k]
-- given
  (f : MvPolynomial (Fin n) k) (P v : Fin n → k) :
-- imply
  totalDerivativeAtLin f P v = totalDerivativeAt f P v := by
-- proof
  apply MvPolynomial.totalDerivativeAtLin_apply


/--
[mem_tangentSpacePoly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/TangentSpace.lean)
-/
@[path]
private lemma mem_tangentSpacePoly_eq
  [Field k]
-- given
  (f : MvPolynomial (Fin n) k) (P v : Fin n → k) :
-- imply
  v ∈ tangentSpacePoly f P ↔ totalDerivativeAt f P v = 0 := by
-- proof
  apply MvPolynomial.mem_tangentSpacePoly


/--
[mem_tangentSpaceIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/TangentSpace.lean)
-/
@[path]
private lemma mem_tangentSpaceIdeal_eq
  [Field k]
-- given
  (I : Ideal (MvPolynomial (Fin n) k)) (P v : Fin n → k) :
-- imply
  v ∈ tangentSpaceIdeal I P ↔ ∀ f ∈ I, totalDerivativeAt f P v = 0 := by
-- proof
  apply MvPolynomial.mem_tangentSpaceIdeal


-- created on 2026-10-09
