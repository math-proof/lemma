import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.JacobiThetaProduct
open MetaMathlibExt.QPochhammer


namespace MetaMathlibExt.QPochhammer

/--
[jacobiThetaProduct_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/JacobiThetaProduct.lean)
-/
@[path]
lemma jacobiThetaProduct_symm
  {x q : ℂ}
-- given
  (hq : ‖q‖ < 1)
  (h0 : q ≠ 0) :
-- imply
  jacobiThetaProduct (q / x) q hq = jacobiThetaProduct x q hq := by
-- proof
  unfold jacobiThetaProduct
  rw [div_div_cancel₀ h0, mul_comm (qPochhammerInf (q / x) q hq) (qPochhammerInf x q hq)]

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[jacobiThetaProduct_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/JacobiThetaProduct.lean)
-/
@[path]
lemma jacobiThetaProduct_zero_left
  {q : ℂ}
-- given
  (hq : ‖q‖ < 1) :
-- imply
  jacobiThetaProduct 0 q hq = qPochhammerInf q q hq := by
-- proof
  simp [jacobiThetaProduct]

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[jacobiThetaProduct_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/JacobiThetaProduct.lean)
-/
@[path]
lemma jacobiThetaProduct_zero_right
  {x : ℂ} :
-- imply
  jacobiThetaProduct x 0 (by simp) = qPochhammerInf x 0 (by simp) := by
-- proof
  simp [jacobiThetaProduct]

end MetaMathlibExt.QPochhammer


-- created on 2026-10-20
-- updated on 2026-10-23
