/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GeneralizedLucasnomialFussCatalanNumber.lean -/


import Def.NumberTheory.GeneralizedLucasnomialFussCatalanNumber
import Lemma.Nat.GeneralizedLucasnomialFussCatalanNumber
import Mathlib.Tactic
import Def.MathlibExtTest.NumberTheory.GeneralizedLucasnomialFussCatalanNumber


namespace MetaMathlibExt

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
