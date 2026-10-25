-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_HomogeneousIdealQuotientGradingInfra.lean: instance decls only.
import Mathlib
import Lemma.AlgebraicGeometry.HomogeneousIdealQuotientGradingInfra

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

/--
info: 'HomogeneousIdealQuotientGrading.pieceHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.pieceHom_coe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.pieceHom_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gradedMonoidOfImages' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.coeAddMonoidHom_map_pieceHom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.preDecompose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.preDecompose_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.preDecompose_apply_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.preDecompose_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.coeAddMonoidHom_preDecompose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.preDecompose_eq_zero_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotDecompose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotDecompose_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.decompositionOfImages' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gradedRingOfImages' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.decompose_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.decompose_mk_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotGrading' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.mem_quotGrading_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.mk_mem_quotGrading' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingPieceHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingPieceHom_coe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingPieceHom_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingGradedMonoid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingGradedRing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingGradedRingOfHomogeneous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.decompose_quotGrading_mk_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.mem_quotGradingSubmodule_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebraOfHomogeneous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.decompose_quotGradingSubmodule_mk_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gateIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gateIdeal_isHomogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gateHomogeneousIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gate_gateIdeal_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gate_mk_X0X1_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gate_X0_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gate_mk_X0_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gate_mk_X0_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gateGradedRing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gateGradedAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'HomogeneousIdealQuotientGrading.gate_decompose_mk_X0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
