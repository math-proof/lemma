/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LucasPolytopicNumber.lean -/


import Def.NumberTheory.LucasPolytopicNumber.Part2
import Lemma.Nat.LucasPolytopicNumber
import Mathlib.Tactic
import Theorem.MathlibExtTest.NumberTheory.LucasPolytopicNumber


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
