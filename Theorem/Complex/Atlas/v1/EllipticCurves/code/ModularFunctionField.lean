module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Abbrev.v1.Atlas.EllipticCurves.code.ModularFunctionField
open CongruenceSubgroup ModularFunctionField


public section

/--
[isModularFunction_of_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularFunctionField.lean)
-/
@[path]
private theorem isModularFunction_of_top_eq
  {f : ℍ → ℂ}
  {Γ : Subgroup SL(2, ℤ)}
-- given
  (hf : IsModularFunction f ⊤) :
-- imply
  IsModularFunction f Γ where meromorphicOnH := by
-- proof
  apply ModularFunctionField.isModularFunction_of_top Γ hf


-- created on 2026-10-23
