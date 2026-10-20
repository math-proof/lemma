import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.PrincipalIdeal
open scoped nonZeroDivisors
open NumberField
open Modulus


/--
[principalRayIdealMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/PrincipalIdeal.lean)
-/
@[path]
private lemma principalRayIdealMap_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  (principalRayIdealMap m x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
    toPrincipalIdeal (𝓞 K) K (x : Kˣ) := by
-- proof
  apply NumberField.Modulus.principalRayIdealMap_apply m x

/--
[toPrincipalIdeal_eq_iff_exists_integralUnit_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/PrincipalIdeal.lean)
-/
@[path]
private lemma toPrincipalIdeal_eq_iff_exists_integralUnit_mul_eq
  [Field K] [NumberField K]
  {x y : Kˣ} :
-- imply
  toPrincipalIdeal (𝓞 K) K x = toPrincipalIdeal (𝓞 K) K y ↔
    ∃ u : (𝓞 K)ˣ,
    x = Units.map (algebraMap (𝓞 K) K).toMonoidHom u * y := by
-- proof
  apply NumberField.Modulus.toPrincipalIdeal_eq_iff_exists_integralUnit_mul x y

/--
[rayGroup_eq_map_rayOneElements](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/PrincipalIdeal.lean)
-/
@[path]
private lemma rayGroup_eq_map_rayOneElements_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  rayGroup m = (rayOneElements m).map (principalRayIdealMap m) := by
-- proof
  apply NumberField.Modulus.rayGroup_eq_map_rayOneElements m


-- created on 2026-10-20
