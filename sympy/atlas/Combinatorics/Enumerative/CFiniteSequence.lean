/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CFiniteSequence.lean -/

import Mathlib.Algebra.MvPolynomial.Basic

/-!
# C-finite polynomial sequences

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL26/Makowsky/makowsky16.tex>.
-/

open scoped BigOperators

namespace MetaMathlibExt

/-- A polynomial sequence is C-finite (concept `jis_sem_35aa465b4e5a8b902eabc445`,
source statement `jis_1ebc476d74ad111e89710ced`):
there exist `k`, `N`, and polynomials `p₁, …, pₖ` in `ZZ[bar{x}]`,
here `MvPolynomial σ ℤ`, such that for all `n ≥ N` the `(n + k + 1)`-st term
equals `∑_{i=1}^k pᵢ` times the `(n + i)`-th term, i.e.
`a (n + k + 1) = ∑ i : Fin k, c i * a (n + i.val + 1)`. -/
def IsCFiniteSequence {σ : Type*} (a : ℕ → MvPolynomial σ ℤ) : Prop :=
  ∃ (k N : ℕ) (c : Fin k → MvPolynomial σ ℤ),
    ∀ n ≥ N, a (n + k + 1) = ∑ i : Fin k, c i * a (n + i.val + 1)

end MetaMathlibExt
