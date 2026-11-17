/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PadicPolynomialDilatation.lean -/

module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Structure.NumberTheory.Padics.PadicPolynomialDilatation

@[expose] public section

/-- Proved witness: dilatation data exists for the constant polynomial one at zero. -/
noncomputable def padicPolynomialDilatation_one_zero (p : ℕ) [Fact p.Prime] :
    PadicPolynomialDilatation p 1 0 where
  exp := 0
  poly := 1
  dilat_eq := by
    simp only [Polynomial.one_comp, Polynomial.map_one, pow_zero, inv_one,
      Polynomial.C_1, mul_one]
  red_ne_zero := by
    simp only [Polynomial.map_one]
    exact one_ne_zero

