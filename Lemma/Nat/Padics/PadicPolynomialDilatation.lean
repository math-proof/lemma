import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.PadicPolynomialDilatation


/--
[padicPolynomialDilatation_exists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PadicPolynomialDilatation.lean)
-/
@[path]
private lemma padicPolynomialDilatation_exists_eq
  {p : ℕ} [Fact p.Prime]
  {f : Polynomial (PadicInt p)}
  {x0 : PadicInt p}
-- given
  (hf : Polynomial.map PadicInt.toZMod f ≠ 0) :
-- imply
  Nonempty (PadicPolynomialDilatation p f x0) := by
-- proof
  apply padicPolynomialDilatation_exists p f x0 hf


-- created on 2026-10-20
