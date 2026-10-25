/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GeneralizedLucasnomialFussCatalanNumber.lean -/


import Def.NumberTheory.GeneralizedLucasnomialFussCatalanNumber
import Lemma.Nat.GeneralizedLucasnomialFussCatalanNumber
import Mathlib.Tactic
import Theorem.MathlibExtTest.NumberTheory.GeneralizedLucasnomialFussCatalanNumber


namespace MetaMathlibExt

noncomputable def countingLucasParams : LucasParameters where
  s := 2
  t := -1
  s_ne_zero := by norm_num
  t_ne_zero := by norm_num
  bracket_ne_zero := by
    intro n hn
    rw [countingLucasBracketAux]
    exact_mod_cast hn

end MetaMathlibExt
