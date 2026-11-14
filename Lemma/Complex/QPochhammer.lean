import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.QPochhammer


namespace MetaMathlibExt.QPochhammer

/--
[QPochhammer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean)
-/
@[path]
private lemma qPochhammerInf_zero_left_eq
-- given
  (q : ℂ)
  (hq : ‖q‖ < 1) :
-- imply
  MetaMathlibExt.QPochhammer.qPochhammerInf 0 q hq = 1 :=
-- proof
  qPochhammerInf_zero_left q hq

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[QPochhammer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean)
-/
@[path]
private lemma hasProd_qPochhammerInf_eq
-- given
  (a q : ℂ)
  (hq : ‖q‖ < 1) :
-- imply
  HasProd (fun n : ℕ => (1 - a * q ^ n))
    (MetaMathlibExt.QPochhammer.qPochhammerInf a q hq) :=
-- proof
  hasProd_qPochhammerInf a q hq

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[QPochhammer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean)
-/
@[path]
private lemma qPochhammerInf_one_zero_eq :
-- imply
  qPochhammerInf 1 0 (by simp) = 0 :=
-- proof
  qPochhammerInf_one_zero

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[QPochhammer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean)
-/
@[path]
private lemma qPochhammerInfRaw_two_one_eq :
-- imply
  qPochhammerInfRaw 2 1 = 1 :=
-- proof
  qPochhammerInfRaw_two_one

end MetaMathlibExt.QPochhammer


-- created on 2026-10-11
-- updated on 2026-10-26
