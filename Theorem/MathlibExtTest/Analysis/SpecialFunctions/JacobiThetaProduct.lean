/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/JacobiThetaProduct.lean -/


import Def.Analysis.SpecialFunctions.JacobiThetaProduct
import Lemma.Real.SpecialFunctions.JacobiThetaProduct
import Mathlib.Tactic.NormNum


namespace MetaMathlibExt.QPochhammer

example (x q : ℂ) (hq : ‖q‖ < 1) :
    jacobiThetaProduct x q hq =
      qPochhammerInf x q hq * qPochhammerInf (q / x) q hq *
        qPochhammerInf q q hq :=
  rfl

example (h : ‖(1 / 2 : ℂ)‖ < 1) :
    jacobiThetaProduct (1 / 4 : ℂ) (1 / 2) h =
      jacobiThetaProduct 2 (1 / 2) h := by
  have h4 : (1 / 2 : ℂ) / 2 = 1 / 4 := by norm_num
  rw [← h4]
  exact jacobiThetaProduct_symm 2 (1 / 2) h (by norm_num)

example (q : ℂ) (hq : ‖q‖ < 1) :
    jacobiThetaProduct 0 q hq = qPochhammerInf q q hq := by simp

example (x : ℂ) :
    jacobiThetaProduct x 0 (by simp) = qPochhammerInf x 0 (by simp) := by simp

example : jacobiThetaProduct (0 : ℂ) 0 (by simp) = 1 := by simp

example : jacobiThetaProduct (1 : ℂ) 0 (by simp) = 0 := by simp

end MetaMathlibExt.QPochhammer
