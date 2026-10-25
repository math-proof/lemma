import Mathlib
import Def.Deformations_LiftFunctor

set_option autoImplicit false

universe u

open CategoryTheory IsLocalRing

namespace Deformation

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G] [TopologicalSpace G]
variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

noncomputable abbrev conjKer (R : ProartinianCat 𝓞) : Subgroup (ConjAct (GL n R)) :=
  ((Matrix.GeneralLinearGroup.map (n := n)
    (ProartinianCat.toResidueField R).hom.toRingHom).ker.comap (ConjAct.ofConjAct.toMonoidHom))

variable (n G 𝓞) in

abbrev mapRepn {A B : ProartinianCat 𝓞} (f : A ⟶ B) (ρ : G →ₜ* GL n A) : G →ₜ* GL n B :=
  (repnFunctor n G 𝓞).map f ρ

section TraceAlgebra

open ProartinianCat

end TraceAlgebra

section TraceConj

end TraceConj

section Universal

open ProartinianCat

end Universal

end Deformation
