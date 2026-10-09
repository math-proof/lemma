import Mathlib
import sympy.Basic
import sympy.Algebra.Polynomial.MestreSquareDecomposition

open MetaMathlibExt

/--
[mestre_monic_square_decomposition_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/MestreSquareDecomposition.lean)
-/
@[path]
private lemma mestre_monic_square_decomposition_general_eq
  [Field K]
-- given
  (hchar : (2 : K) ≠ 0) {d : ℕ} {P : Polynomial K}
  (hPmonic : P.Monic) (hPdeg : P.natDegree = 2 * d + 2) :
-- imply
  ∃! p : Polynomial K × Polynomial K,
    p.1.Monic ∧ p.1.natDegree = d + 1 ∧ P = p.1 ^ 2 - p.2 ∧ p.2.degree ≤ ↑d := by
-- proof
  apply mestre_monic_square_decomposition_general
  · exact hchar
  · exact hPmonic
  · exact hPdeg


/--
[mestre_monic_square_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/MestreSquareDecomposition.lean)
-/
@[path]
private lemma mestre_monic_square_decomposition_eq
  [Field K]
-- given
  (hchar : (2 : K) ≠ 0) {d : ℕ} (hd : 0 < d)
  {P : Polynomial K} (hPmonic : P.Monic) (hPdeg : P.natDegree = 2 * d + 2) :
-- imply
  ∃! p : Polynomial K × Polynomial K,
    p.1.Monic ∧ p.1.natDegree = d + 1 ∧ P = p.1 ^ 2 - p.2 ∧ p.2.degree ≤ ↑d := by
-- proof
  apply mestre_monic_square_decomposition
  · exact hchar
  · exact hd
  · exact hPmonic
  · exact hPdeg


-- created on 2026-10-09
