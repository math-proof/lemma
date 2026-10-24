/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/LambertWFunction.lean -/


import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import sympy.atlas.Analysis.SpecialFunctions.LambertWFunction

namespace MetaMathlibExt

example : lambertMap 0 = 0 := by
  simp [lambertMap]

example : lambertMap (-1) = -Real.exp (-1) := by
  simp [lambertMap]

example : ∃! y : { y : ℝ // -1 < y }, lambertMap y.val = 0 := by
  apply existsUnique_lambertMap_preimage 0
  have h := Real.exp_pos (-1)
  linarith

example (y : { y : ℝ // -1 < y }) (hy : lambertMap y.val = 0) : y.val = 0 := by
  have hx : -Real.exp (-1) < (0 : ℝ) := by
    have h := Real.exp_pos (-1)
    linarith
  have hU := existsUnique_lambertMap_preimage 0 hx
  have h0 : lambertMap (⟨0, by norm_num⟩ : { y : ℝ // -1 < y }).val = 0 := by
    simp [lambertMap]
  have heq := hU.unique hy h0
  exact congrArg Subtype.val heq

end MetaMathlibExt
