/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GeneralizedLucasnomialFussCatalanNumber.lean -/


import sympy.atlas.NumberTheory.GeneralizedLucasnomialFussCatalanNumber
import Lemma.Nat.GeneralizedLucasnomialFussCatalanNumber
import Mathlib.Tactic

namespace MetaMathlibExt

private theorem countingLucasBracketAux (n : ℕ) :
    lucasBracketAux 2 (-1) n = (n : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [lucasBracketAux]
  | one => norm_num [lucasBracketAux]
  | more n ih0 ih1 =>
      rw [lucasBracketAux, ih0, ih1]
      push_cast
      ring

private noncomputable def countingLucasParams : LucasParameters where
  s := 2
  t := -1
  s_ne_zero := by norm_num
  t_ne_zero := by norm_num
  bracket_ne_zero := by
    intro n hn
    rw [countingLucasBracketAux]
    exact_mod_cast hn

example (P : LucasParameters) :
    generalizedLucasnomialFussCatalan P 2 1 1 =
      (lucasBracket P 1 / lucasBracket P 2) * lucasnomial P 2 1 := rfl

example : generalizedLucasnomialFussCatalan countingLucasParams 2 1 1 = 1 := by
  norm_num [generalizedLucasnomialFussCatalan, lucasnomial, lucasFactorial,
    lucasBracket, lucasBracketAux, countingLucasParams, Finset.prod_range_succ]

example (P : LucasParameters) (a r n : ℕ) :
    generalizedLucasnomialFussCatalan P a r n =
      generalizedLucasnomialFussCatalanRS P a r n := rfl

example (P : LucasParameters) (r n : ℕ) :
    generalizedLucasnomialFussCatalan P 0 r n =
      (lucasBracket P r / lucasBracket P ((0 - 1) * n + r)) *
        lucasnomial P (0 * n + r - 1) n := rfl

end MetaMathlibExt
