-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_HomogeneousIdealQuotientGradingInfra.lean: instance decls only.
import Mathlib
import Lemma.Ideal.HomogeneousIdealQuotientGradingInfra

namespace HomogeneousIdealQuotientGrading

open DirectSum


section QuotGradingDef

variable {ι A σ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ)
variable (I : Ideal A)

instance quotGradingGradedMonoid [AddMonoid ι] [SetLike.GradedMonoid 𝒜] :
    SetLike.GradedMonoid (quotGrading 𝒜 I) :=
  gradedMonoidOfImages 𝒜 I (quotGrading 𝒜 I)
    (fun _ _ ha => mk_mem_quotGrading 𝒜 I ha)
    (fun _ _ hb => (mem_quotGrading_iff 𝒜 I).mp hb)

end QuotGradingDef

section QuotGradingGraded

variable {ι A σ : Type*}
variable [DecidableEq ι] [AddMonoid ι] [CommRing A]
variable [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
variable (I : Ideal A)

instance quotGradingGradedRingOfHomogeneous (J : HomogeneousIdeal 𝒜) :
    GradedRing (quotGrading 𝒜 J.toIdeal) :=
  quotGradingGradedRing 𝒜 J.toIdeal J.isHomogeneous

end QuotGradingGraded

section SubmoduleVersion

variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A)
variable (I : Ideal A)

instance quotGradingSubmoduleGradedMonoid [AddMonoid ι] [SetLike.GradedMonoid 𝒜] :
    SetLike.GradedMonoid (quotGradingSubmodule 𝒜 I) :=
  gradedMonoidOfImages 𝒜 I (quotGradingSubmodule 𝒜 I)
    (fun _ _ ha => mk_mem_quotGradingSubmodule 𝒜 I ha)
    (fun _ _ hb => (mem_quotGradingSubmodule_iff 𝒜 I).mp hb)

variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]

instance quotGradingSubmoduleGradedAlgebraOfHomogeneous (J : HomogeneousIdeal 𝒜) :
    GradedAlgebra (quotGradingSubmodule 𝒜 J.toIdeal) :=
  quotGradingSubmoduleGradedAlgebra 𝒜 J.toIdeal J.isHomogeneous

end SubmoduleVersion


end HomogeneousIdealQuotientGrading

