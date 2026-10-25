/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/NarayanaPolynomial.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Def.Combinatorics.Enumerative.NarayanaNumber
import Lemma.Finset.Enumerative.NarayanaNumber
/-!
# Narayana polynomials with zero constant term

This module extends the Narayana-number API with the polynomial normalization
used by the cited Journal of Integer Sequences sources.
-/


namespace MetaMathlibExt

/-- Narayana-polynomial coefficients in the normalization with row zero equal
to `[1]` and every positive row having zero constant term.

Concept `jis_sem_06bee1249c32868dc6d7f8d6`; source statements
`jis_6e879284923110cb216e6b7f`, `jis_fe161627e1c6dd385c4aac22`,
`jis_dc822bf3838116b320b91d53`, and `jis_8759141f567e62dd523678c2`.
The positive-index case deliberately reuses `narayana` from the prerequisite
Narayana-number API. -/
def narayanaPolynomialCoeff : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => narayana ⟨n + 1, Nat.succ_pos n⟩ ⟨k + 1, Nat.succ_pos k⟩

/-- The Narayana row-generating polynomial with zero constant coefficient in
positive rows.

Concept `jis_sem_06bee1249c32868dc6d7f8d6`; the source normalization begins
`1`, `X`, `X² + X`, `X³ + 3X² + X`, and uses the finite sum
`N_n(X) = ∑_{k=0}^n N(n,k) X^k`. -/
noncomputable def narayanaPolynomial (R : Type*) [Semiring R] (n : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (narayanaPolynomialCoeff n k : R) * Polynomial.X ^ k

end MetaMathlibExt
