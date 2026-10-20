import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.JacobiThetaProduct
open MetaMathlibExt.QPochhammer


/--
[jacobiThetaProduct_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/JacobiThetaProduct.lean)
-/
@[path]
private lemma jacobiThetaProduct_symm_eq
  {x q : ℂ}
-- given
  (hq : ‖q‖ < 1)
  (h0 : q ≠ 0) :
-- imply
  jacobiThetaProduct (q / x) q hq = jacobiThetaProduct x q hq := by
-- proof
  apply MetaMathlibExt.QPochhammer.jacobiThetaProduct_symm x q hq h0

/--
[jacobiThetaProduct_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/JacobiThetaProduct.lean)
-/
@[path]
private lemma jacobiThetaProduct_zero_left_eq
  {q : ℂ}
-- given
  (hq : ‖q‖ < 1) :
-- imply
  jacobiThetaProduct 0 q hq = qPochhammerInf q q hq := by
-- proof
  apply MetaMathlibExt.QPochhammer.jacobiThetaProduct_zero_left q hq

/--
[jacobiThetaProduct_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/JacobiThetaProduct.lean)
-/
@[path]
private lemma jacobiThetaProduct_zero_right_eq
  {x : ℂ} :
-- imply
  jacobiThetaProduct x 0 (by simp) = qPochhammerInf x 0 (by simp) := by
-- proof
  apply MetaMathlibExt.QPochhammer.jacobiThetaProduct_zero_right x


-- created on 2026-10-20
