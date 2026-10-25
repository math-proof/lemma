import Mathlib
import Class.Deformations_ProartinianCat
import Def.CategoryTheory_Subfunctor_OfIsTerminal
import Def.Deformations_LiftFunctor

set_option autoImplicit false

open CategoryTheory IsLocalRing

namespace Deformation

universe u

variable {n : Type} [Fintype n] [DecidableEq n] (G : Type u) [Group G] [TopologicalSpace G]
variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]


omit [IsLocalRing 𝓞] in
@[simp]
lemma repnFunctor_map {R S : ProartinianCat 𝓞} (f : R ⟶ S) (ρ : G →ₜ* GL n R) (x : G) :
    DFunLike.coe (F := G →ₜ* GL n S) ((repnFunctor n G 𝓞).map f ρ) x =
      Matrix.GeneralLinearGroup.map (n := n) f.hom.toRingHom (ρ x) := rfl

end Deformation
