/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LucasPolytopicNumber.lean -/
module

public import Def.NumberTheory.LucasPolytopicNumber.Part2
public import Theorem.Nat.LucasPolytopicNumber
public import Mathlib.Tactic

public section

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
