/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/QRDowlingPolynomial.lean -/
module

public import Def.NumberTheory.QRDowlingPolynomial
public import Theorem.Nat.QRDowlingPolynomial
open MetaMathlibExt

public section

example (W : ℕ → ℕ → ℕ) (n : ℕ) :
    qrDowlingNumber W n = ∑ k ∈ Finset.range (n + 1), W n k :=
  qrDowlingNumber_eq_sum W n

