/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GeneralizedLucasnomialFussCatalanNumber.lean -/

module

public import Def.NumberTheory.GeneralizedLucasnomialFussCatalanNumber
public import Theorem.Nat.GeneralizedLucasnomialFussCatalanNumber
public import Mathlib.Tactic
public import Theorem.MathlibExtTest.NumberTheory.GeneralizedLucasnomialFussCatalanNumber

@[expose] public section

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
