/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LucasPolytopicNumber.lean -/


import Def.NumberTheory.LucasPolytopicNumber.Part2
import Lemma.Nat.LucasPolytopicNumber
import Mathlib.Tactic


namespace MetaMathlibExt

theorem naturalLucasBracketAux (n : ℕ) :
    lucasBracketAux 2 (-1) n = (n : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [lucasBracketAux]
  | one => norm_num [lucasBracketAux]
  | more n ih0 ih1 =>
      rw [lucasBracketAux, ih0, ih1]
      push_cast
      ring

end MetaMathlibExt
