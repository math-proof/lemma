/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/QRDowlingPolynomial.lean -/


import sympy.atlas.NumberTheory.QRDowlingPolynomial
import Lemma.Nat.QRDowlingPolynomial

open MetaMathlibExt

example (W : ℕ → ℕ → ℕ) (n : ℕ) :
    qrDowlingNumber W n = ∑ k ∈ Finset.range (n + 1), W n k :=
  qrDowlingNumber_eq_sum W n
