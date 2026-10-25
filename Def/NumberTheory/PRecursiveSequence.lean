/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PRecursiveSequence.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
open scoped BigOperators


namespace MetaMathlibExt

/-!
# P-recursive integer sequences

Source: C. Banderier and F. Luca, *On the Period mod m of Polynomially-Recursive
Sequences: a Case Study*, Journal of Integer Sequences 22 (2019),
[`band3.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL22/Banderier/band3.tex).
-/

/-- An integer sequence is P-recursive of order `r` with coefficient polynomials
`P₀, …, Pᵣ` if, for every `n ≥ r`,
`P₀(n) uₙ = ∑_{i=1}^r Pᵢ(n) uₙ₋ᵢ`.

The finite coefficient family prevents accidental access beyond `Pᵣ`, and the explicit
index guard records the source domain without relying on truncated subtraction. -/
def IsPRecursiveSequence (r : ℕ) (P : Fin (r + 1) → Polynomial ℤ)
    (u : ℕ → ℤ) : Prop :=
  ∀ n, r ≤ n →
    (P 0).eval (n : ℤ) * u n =
      ∑ i : Fin r, (P i.succ).eval (n : ℤ) * u (n - (i + 1))

end MetaMathlibExt
