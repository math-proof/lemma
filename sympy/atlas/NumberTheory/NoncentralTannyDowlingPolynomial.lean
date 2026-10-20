/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NoncentralTannyDowlingPolynomial.lean -/

import Mathlib.Algebra.Polynomial.Basic

namespace MetaMathlibExt

variable {R : Type*} [CommRing R]

/-- Noncentral Whitney numbers of the second kind, concept
`jis_term_6c385244500b53dde9d3f070`, source
`https://cs.uwaterloo.ca/journals/JIS/VOL24/Mangontarum/mang13.tex`, SHA-256
`e08f5454236c4aeb678d73ad15de5b19ce88cfbffc855ad2a25e45309b533cc5`, recurrence
underlying the Tanny-Dowling polynomial in equation (6). -/
def noncentralWhitneySecond (m a : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => (-a) ^ (n + 1)
  | n + 1, k + 1 =>
    noncentralWhitneySecond m a n k +
      (m * ((k + 1 : ℕ) : R) - a) * noncentralWhitneySecond m a n (k + 1)

/-- Noncentral Tanny-Dowling polynomial, equation (6), concept
`jis_term_6c385244500b53dde9d3f070`, source
`https://cs.uwaterloo.ca/journals/JIS/VOL24/Mangontarum/mang13.tex`, SHA-256
`e08f5454236c4aeb678d73ad15de5b19ce88cfbffc855ad2a25e45309b533cc5`. -/
noncomputable def noncentralTannyDowlingPolynomial (m a : R) (n : ℕ) : Polynomial R :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    Polynomial.C (((Nat.factorial k : ℕ) : R) * noncentralWhitneySecond m a n k) *
      Polynomial.X ^ k

end MetaMathlibExt
