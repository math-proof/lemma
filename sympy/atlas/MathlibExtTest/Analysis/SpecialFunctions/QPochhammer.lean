/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/QPochhammer.lean -/


import sympy.atlas.Analysis.SpecialFunctions.QPochhammer
import Lemma.Complex.QPochhammer

namespace MetaMathlibExt.QPochhammer

example (a q : ℂ) :
    qPochhammerInfRaw a q = ∏' n : ℕ, (1 - a * q ^ n) := rfl

example (a q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInf a q hq = ∏' n : ℕ, (1 - a * q ^ n) := rfl

example (a : ℂ) :
    HasProd (fun n : ℕ => (1 - a * (0 : ℂ) ^ n))
      (qPochhammerInf a 0 (by simp)) :=
  hasProd_qPochhammerInf a 0 (by simp)

example :
    HasProd (fun n : ℕ => (1 - (1 : ℂ) * (0 : ℂ) ^ n))
      (qPochhammerInf 1 0 (by simp)) :=
  hasProd_qPochhammerInf 1 0 (by simp)

example : qPochhammerInf 1 0 (by simp) = 0 := by simp

example (q : ℂ) (hq : ‖q‖ < 1) : qPochhammerInf 0 q hq = 1 := by simp

example (q : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => (1 - (0 : ℂ) * q ^ n))
      (qPochhammerInf 0 q hq) :=
  hasProd_qPochhammerInf 0 q hq

example : qPochhammerInfRaw 2 1 = 1 := qPochhammerInfRaw_two_one

end MetaMathlibExt.QPochhammer
