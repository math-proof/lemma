import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.EllipticCurves.code.ModularFunctionField
open CongruenceSubgroup ModularFunctionField


/--
[isModularFunction_of_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularFunctionField.lean)
-/
@[path]
private lemma isModularFunction_of_top_eq
  {f : ℍ → ℂ}
  {Γ : Subgroup SL(2, ℤ)}
-- given
  (hf : IsModularFunction f ⊤) :
-- imply
  IsModularFunction f Γ where meromorphicOnH := by
-- proof
  apply ModularFunctionField.isModularFunction_of_top Γ hf


-- created on 2026-10-23
