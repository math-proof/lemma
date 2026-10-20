import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GeneralizedLucasnomialFussCatalan
open MetaMathlibExt


/--
[generalized_lucasnomial_fuss_catalan_integral_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucasnomialFussCatalan.lean)
-/
@[path]
private lemma generalized_lucasnomial_fuss_catalan_integral_general_eq
  {P Q : ℤ}
  {U : ℕ → ℤ}
  {r a n : ℕ}
-- given
  (hU : IsLucasSequenceFirstKind P Q U)
  (hnondeg : ∀ n : ℕ, n ≥ 1 → U n ≠ 0)
  (hreg : Int.gcd P Q = 1)
  (hr : r ≥ 1)
  (ha : a ≥ 2)
  (hn : n ≥ 1) :
-- imply
  ∃ z : ℤ,
    ((U r : ℚ) / ((U ((a - 1) * n + r)) : ℚ)) *
    ((∏ j ∈ Finset.range n, ((U (a * n + r - 1 - j)) : ℚ)) /
    (∏ j ∈ Finset.range n, ((U (j + 1)) : ℚ))) =
    ((z : ℚ)) := by
-- proof
  apply MetaMathlibExt.generalized_lucasnomial_fuss_catalan_integral_general hU hnondeg hreg r a hr ha n hn

/--
[generalized_lucasnomial_fuss_catalan_integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucasnomialFussCatalan.lean)
-/
@[path]
private lemma generalized_lucasnomial_fuss_catalan_integral_eq
  {P Q : ℤ}
  {U : ℕ → ℤ}
  {r a n : ℕ}
-- given
  (hP : P ≠ 0)
  (hQ : Q ≠ 0)
  (hU0 : U 0 = 0)
  (hU1 : U 1 = 1)
  (hUrec : ∀ n : ℕ, U (n + 2) = P * U (n + 1) - Q * U n)
  (hnondeg : ∀ n : ℕ, n ≥ 1 → U n ≠ 0)
  (hreg : Int.gcd P Q = 1)
  (hr : r ≥ 1)
  (ha : a ≥ 2)
  (hn : n ≥ 1) :
-- imply
  ∃ z : ℤ,
    ((U r : ℚ) / ((U ((a - 1) * n + r)) : ℚ)) *
    ((∏ j ∈ Finset.range n, ((U (a * n + r - 1 - j)) : ℚ)) /
    (∏ j ∈ Finset.range n, ((U (j + 1)) : ℚ))) =
    ((z : ℚ)) := by
-- proof
  apply MetaMathlibExt.generalized_lucasnomial_fuss_catalan_integral P Q U r a hP hQ hU0 hU1 hUrec hnondeg hreg hr ha n hn


-- created on 2026-10-20
