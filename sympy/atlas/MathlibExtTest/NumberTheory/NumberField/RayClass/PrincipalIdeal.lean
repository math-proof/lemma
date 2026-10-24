/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/PrincipalIdeal.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.PrincipalIdeal
import Lemma.Nat.NumberField.RayClass.PrincipalIdeal

@[expose] public noncomputable section

open scoped nonZeroDivisors
open NumberField

namespace N406PrincipalIdealTest

variable {K : Type*} [Field K] [NumberField K]

-- Map application unfolds to the principal ideal of the underlying unit.
example (m : Modulus K) (x : Modulus.rayElements m) :
    (Modulus.principalRayIdealMap m x :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toPrincipalIdeal (𝓞 K) K (x : Kˣ) :=
  Modulus.principalRayIdealMap_apply m x

-- Identity boundary: the map sends `1` to `1`.
example (m : Modulus K) :
    Modulus.principalRayIdealMap m 1 = 1 :=
  map_one _

-- Forward direction of the integral-unit equality iff.
example (x y : Kˣ)
    (h : toPrincipalIdeal (𝓞 K) K x =
      toPrincipalIdeal (𝓞 K) K y) :
    ∃ u : (𝓞 K)ˣ,
      x = Units.map (algebraMap (𝓞 K) K).toMonoidHom u * y :=
  (Modulus.toPrincipalIdeal_eq_iff_exists_integralUnit_mul x y).mp h

-- Reverse direction of the integral-unit equality iff.
example (x y : Kˣ) (u : (𝓞 K)ˣ)
    (h : x = Units.map (algebraMap (𝓞 K) K).toMonoidHom u * y) :
    toPrincipalIdeal (𝓞 K) K x =
      toPrincipalIdeal (𝓞 K) K y :=
  (Modulus.toPrincipalIdeal_eq_iff_exists_integralUnit_mul x y).mpr ⟨u, h⟩

-- Reflexivity boundary of the equality iff.
example (x : Kˣ) :
    ∃ u : (𝓞 K)ˣ,
      x = Units.map (algebraMap (𝓞 K) K).toMonoidHom u * x :=
  (Modulus.toPrincipalIdeal_eq_iff_exists_integralUnit_mul x x).mp rfl

-- Ray-group equality with the image of ray-one elements.
example (m : Modulus K) :
    Modulus.rayGroup m =
      (Modulus.rayOneElements m).map (Modulus.principalRayIdealMap m) :=
  Modulus.rayGroup_eq_map_rayOneElements m

-- Membership consequence of the ray-group equality.
example (m : Modulus K) (x : Modulus.rayElements m)
    (h : x ∈ Modulus.rayOneElements m) :
    Modulus.principalRayIdealMap m x ∈ Modulus.rayGroup m := by
  rw [Modulus.rayGroup_eq_map_rayOneElements]
  exact Subgroup.mem_map_of_mem _ h

end N406PrincipalIdealTest
