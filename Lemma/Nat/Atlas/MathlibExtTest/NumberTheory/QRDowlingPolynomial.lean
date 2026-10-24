import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.NumberTheory.QRDowlingPolynomial
open MetaMathlibExt


/--
[test_poly_n0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/QRDowlingPolynomial.lean)
-/
@[path]
private lemma test_poly_n0 :
  qrDowlingPolynomial (R := ℕ) (fun _ k => k + 1) 0 = Polynomial.C 1 := by
  simp [qrDowlingPolynomial]

/--
[test_zero_family](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/QRDowlingPolynomial.lean)
-/
@[path]
private lemma test_zero_family :
  qrDowlingPolynomial (R := ℕ) (fun _ _ => 0) 2 = 0 := by
  simp [qrDowlingPolynomial]

/--
[test_poly_n1_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/QRDowlingPolynomial.lean)
-/
@[path]
private lemma test_poly_n1_boundary :
  qrDowlingPolynomial (R := ℕ) (fun _ k => if k = 1 then 1 else 0) 1 =
    Polynomial.X := by
  simp [qrDowlingPolynomial]

/--
[test_number_n0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/QRDowlingPolynomial.lean)
-/
@[path]
private lemma test_number_n0 :
  qrDowlingNumber (R := ℕ) (fun _ k => k + 1) 0 = 1 := by
  simp [qrDowlingNumber_eq_sum]


-- created on 2026-10-23
