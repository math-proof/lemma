import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Def2213
open RayClassField
open scoped NumberField


namespace RayClassField

/--
[RayClassChar.rayGroup_le_kernelSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Def2213.lean)
-/
@[path]
lemma RayClassChar.rayGroup_le_kernelSubgroup
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {χ : RayClassChar K 𝔪} :
-- imply
  RayGroup K 𝔪 ≤ χ.kernelSubgroup := by
-- proof
  intro x hx
  show toRayClass K 𝔪 x ∈ MonoidHom.ker χ
  rw [MonoidHom.mem_ker]
  have : toRayClass K 𝔪 x = 1 := by
    show (QuotientGroup.mk' (RayGroup K 𝔪)) x = 1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [this, map_one]

end RayClassField

namespace RayClassField

/--
[RayClassChar.conductor_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Def2213.lean)
-/
@[path]
lemma RayClassChar.conductor_dvd
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {χ : RayClassChar K 𝔪} :
-- imply
  χ.conductor.dvd 𝔪 :=
-- proof
  χ.kernelCongruenceSubgroup.conductor_dvd

end RayClassField


-- created on 2026-10-23
