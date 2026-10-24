import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_CuspForm_QCoeffLinear
import Lemma.Int.P2MUtil


/--
[CuspForm_qCoeffLinear_apply](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CuspForm_qCoeffLinear_apply.lean)
-/
@[path]
private lemma main
  {M : ℕ}
  {k : ℤ}
  {n : ℕ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 M) k} :
-- imply
  CuspForm.qCoeffLinear M k n f = ModularFormClass.qCoeff (⇑f) n :=
-- proof
  rfl


-- created on 2026-10-23
