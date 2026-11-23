/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LucasPolytopicNumber.lean -/

module

public import Def.NumberTheory.LucasPolytopicNumber.Part2
public import Theorem.Nat.LucasPolytopicNumber
public import Mathlib.Tactic
public import Theorem.MathlibExtTest.NumberTheory.LucasPolytopicNumber

@[expose] public section

namespace MetaMathlibExt

noncomputable def naturalLucasParameters : LucasParameters where
  s := 2
  t := -1
  s_ne_zero := by norm_num
  t_ne_zero := by norm_num
  bracket_ne_zero := by
    intro n hn
    rw [naturalLucasBracketAux]
    exact_mod_cast hn

end MetaMathlibExt
