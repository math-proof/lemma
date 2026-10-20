import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.OddPerfectPolynomial
open MetaMathlibExt


/--
[odd_perfect_polynomial_is_square](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/OddPerfectPolynomial.lean)
-/
@[path]
private lemma odd_perfect_polynomial_is_square_eq
  {A : Polynomial (ZMod 2)}
-- given
  (hodd : IsCoprime A Polynomial.X ∧ IsCoprime A (Polynomial.X + 1))
  (hperfect : (finsum fun d : {d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A} => (d : Polynomial (ZMod 2))) = A) :
-- imply
  IsSquare A := by
-- proof
  apply MetaMathlibExt.odd_perfect_polynomial_is_square A hodd hperfect


-- created on 2026-10-20
