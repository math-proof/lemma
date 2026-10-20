/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/RealCyclotomicPolynomial.lean -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Minpoly.Basic

/-!
# Real cyclotomic polynomial — support definition
-/

namespace MetaMathlibExt

/-- The real cyclotomic polynomial: the minimal polynomial over `ℤ` of the canonical
root trace `ζ + ζ⁻¹`, where `ζ = Complex.exp (2 * π * I / n)`. Totalized for all `n`;
later mathematical claims about this polynomial require `n > 2`.

Source: Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials of
Algebraic Cosine Values at Rational Multiples of π", Journal of Integer Sequences 19
(2016), source lines 83-90:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex
source SHA-256 15e6923301658b132cd14eb587f480152fbf9dd9554ecbc6ce321216d9314455
normalized no-final-newline span SHA-256
e91ccd0347f84043d402747f2c4aaf5e6d5f22cba3840369c7fb8a8732dbe039 -/
noncomputable def realCyclotomicPolynomial (n : ℕ) : Polynomial ℤ :=
  minpoly ℤ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) +
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)))⁻¹)

end MetaMathlibExt
