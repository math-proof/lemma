import Mathlib
import sympy.Basic

open Polynomial

/--
[Polynomial_aeval_pow_card_eq_pow_card](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_aeval_pow_card_eq_pow_card.lean)
-/
@[main]
private lemma main
  [Field F] [Fintype F] [CommRing E] [Algebra F E]
  {p : F[X]}
  {x : E} :
-- imply
  Polynomial.aeval (x ^ Fintype.card F) p = (Polynomial.aeval x p) ^ Fintype.card F := by
-- proof
  rw [← Polynomial.expand_aeval (Fintype.card F) p x, FiniteField.expand_card, map_pow]


-- created on 2026-10-03
