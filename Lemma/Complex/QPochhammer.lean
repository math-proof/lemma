import Mathlib
import sympy.Basic
import sympy.functions.special.QPochhammer


/--
[QPochhammer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean)
-/
@[path]
private lemma q_pochhammer_inf_zero_left_eq
-- given
  (q : ℂ)
  (hq : ‖q‖ < 1) :
-- imply
  MetaMathlibExt.QPochhammer.qPochhammerInf 0 q hq = 1 := by
-- proof
  apply MetaMathlibExt.QPochhammer.qPochhammerInf_zero_left q hq

/--
[QPochhammer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean)
-/
@[path]
private lemma has_prod_q_pochhammer_inf_is
-- given
  (a q : ℂ)
  (hq : ‖q‖ < 1) :
-- imply
  HasProd (fun n : ℕ => (1 - a * q ^ n))
    (MetaMathlibExt.QPochhammer.qPochhammerInf a q hq) := by
-- proof
  apply MetaMathlibExt.QPochhammer.hasProd_qPochhammerInf a q hq

/--
[QPochhammer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean)
-/
@[path]
private lemma q_pochhammer_inf_one_zero_eq
-- given
  (hq : ‖(0 : ℂ)‖ < 1) :
-- imply
  MetaMathlibExt.QPochhammer.qPochhammerInf 1 0 hq = 0 := by
-- proof
  apply MetaMathlibExt.QPochhammer.qPochhammerInf_one_zero

/--
[QPochhammer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean)
-/
@[path]
private lemma q_pochhammer_inf_raw_two_one_eq :
-- imply
  MetaMathlibExt.QPochhammer.qPochhammerInfRaw 2 1 = 1 := by
-- proof
  apply MetaMathlibExt.QPochhammer.qPochhammerInfRaw_two_one


-- created on 2026-10-11
