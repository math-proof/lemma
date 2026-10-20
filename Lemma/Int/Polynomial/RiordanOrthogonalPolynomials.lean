import Mathlib
import sympy.Basic
import sympy.atlas.Algebra.Polynomial.RiordanOrthogonalPolynomials
open MetaMathlibExt


/--
[riordan_coeff_orth_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RiordanOrthogonalPolynomials.lean)
-/
@[path]
private lemma riordan_coeff_orth_equiv_eq
  :
-- imply
  ∀ (d h : PowerSeries ℝ) (L : ℕ → ℕ → ℝ),
    (PowerSeries.coeff 0 h = 0 ∧ PowerSeries.coeff 1 h ≠ 0 ∧
    PowerSeries.coeff 0 d ≠ 0 ∧
    ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k)) →
    let IsMonicOrthogonalCoeffArray := by
-- proof
  apply MetaMathlibExt.riordan_coeff_orth_equiv


-- created on 2026-10-20
