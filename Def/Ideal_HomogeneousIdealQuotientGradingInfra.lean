import Mathlib
import Instance.AlgebraicGeometry_HomogeneousIdealQuotientGradingInfra

namespace HomogeneousIdealQuotientGrading

open DirectSum

section Engine

variable {ι A σ τ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
variable (I : Ideal A)
variable [SetLike τ (A ⧸ I)] [AddSubmonoidClass τ (A ⧸ I)] (ℬ : ι → τ)

def pieceHom (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (i : ι) :
    𝒜 i →+ ℬ i :=
  AddMonoidHom.codRestrict
    ((Ideal.Quotient.mk I).toAddMonoidHom.comp (AddSubmonoidClass.subtype (𝒜 i))) (ℬ i)
    (fun a => hmem i a a.2)

variable [DecidableEq ι]

variable [AddMonoid ι] [GradedRing 𝒜]

def preDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) :
    A →+ ⨁ i, ℬ i :=
  (DirectSum.map (pieceHom 𝒜 I ℬ hmem)).comp (decomposeAddEquiv 𝒜).toAddMonoidHom

def quotDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (hI : I.IsHomogeneous 𝒜) : A ⧸ I →+ ⨁ i, ℬ i :=
  QuotientAddGroup.lift I.toAddSubgroup (preDecompose 𝒜 I ℬ hmem)
    (fun _ ha => preDecompose_eq_zero_of_mem 𝒜 I ℬ hmem hI ha)

@[reducible] def decompositionOfImages
    (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b)
    (hI : I.IsHomogeneous 𝒜) : DirectSum.Decomposition ℬ :=
  DirectSum.Decomposition.ofAddHom ℬ (quotDecompose 𝒜 I ℬ hmem hI)
    (by
      refine AddMonoidHom.ext fun x => ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, quotDecompose_mk,
        coeAddMonoidHom_preDecompose])
    (by
      refine DirectSum.addHom_ext fun i b => ?_
      rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, DirectSum.coeAddMonoidHom_of]
      obtain ⟨a, ha, hab⟩ := hsurj i (b : A ⧸ I) b.2
      rw [← hab, quotDecompose_mk, preDecompose_of_mem 𝒜 I ℬ hmem ha]
      exact congrArg _ (Subtype.ext hab))

@[reducible] def gradedRingOfImages
    (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b)
    (hI : I.IsHomogeneous 𝒜) : GradedRing ℬ where
  toGradedMonoid := gradedMonoidOfImages 𝒜 I ℬ hmem hsurj
  toDecomposition := decompositionOfImages 𝒜 I ℬ hmem hsurj hI

end Engine

section QuotGradingDef

variable {ι A σ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ)
variable (I : Ideal A)

def quotGrading (i : ι) : AddSubgroup (A ⧸ I) :=
  (AddSubgroup.ofClass (𝒜 i)).map (Ideal.Quotient.mk I).toAddMonoidHom

def quotGradingPieceHom (i : ι) : 𝒜 i →+ quotGrading 𝒜 I i :=
  pieceHom 𝒜 I (quotGrading 𝒜 I) (fun _ _ ha => mk_mem_quotGrading 𝒜 I ha) i

end QuotGradingDef

section QuotGradingGraded

variable {ι A σ : Type*}
variable [DecidableEq ι] [AddMonoid ι] [CommRing A]
variable [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
variable (I : Ideal A)

@[reducible] def quotGradingGradedRing (hI : I.IsHomogeneous 𝒜) :
    GradedRing (quotGrading 𝒜 I) :=
  gradedRingOfImages 𝒜 I (quotGrading 𝒜 I)
    (fun _ _ ha => mk_mem_quotGrading 𝒜 I ha)
    (fun _ _ hb => (mem_quotGrading_iff 𝒜 I).mp hb)
    hI

end QuotGradingGraded

section SubmoduleVersion

variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A)
variable (I : Ideal A)

def quotGradingSubmodule (i : ι) : Submodule R (A ⧸ I) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap

variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]

@[reducible] def quotGradingSubmoduleGradedAlgebra (hI : I.IsHomogeneous 𝒜) :
    GradedAlgebra (quotGradingSubmodule 𝒜 I) :=
  gradedRingOfImages 𝒜 I (quotGradingSubmodule 𝒜 I)
    (fun _ _ ha => mk_mem_quotGradingSubmodule 𝒜 I ha)
    (fun _ _ hb => (mem_quotGradingSubmodule_iff 𝒜 I).mp hb)
    hI

end SubmoduleVersion

section Gate

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def gateIdeal : Ideal (MvPolynomial (Fin 2) ℤ) :=
  Ideal.span {(X 0 * X 1 : MvPolynomial (Fin 2) ℤ)}

noncomputable def gateHomogeneousIdeal :
    HomogeneousIdeal (homogeneousSubmodule (Fin 2) ℤ) :=
  ⟨gateIdeal, gateIdeal_isHomogeneous⟩

@[reducible] noncomputable def gateGradedRing :
    GradedRing (quotGrading (homogeneousSubmodule (Fin 2) ℤ) gateIdeal) :=
  quotGradingGradedRing _ _ gateIdeal_isHomogeneous

@[reducible] noncomputable def gateGradedAlgebra :
    GradedAlgebra (quotGradingSubmodule (homogeneousSubmodule (Fin 2) ℤ) gateIdeal) :=
  quotGradingSubmoduleGradedAlgebra _ _ gateIdeal_isHomogeneous

end Gate

end HomogeneousIdealQuotientGrading

/--
info: 'HomogeneousIdealQuotientGrading.pieceHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.pieceHom

/--
info: 'HomogeneousIdealQuotientGrading.pieceHom_coe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.pieceHom_coe

/--
info: 'HomogeneousIdealQuotientGrading.pieceHom_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.pieceHom_surjective

/--
info: 'HomogeneousIdealQuotientGrading.gradedMonoidOfImages' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gradedMonoidOfImages

/--
info: 'HomogeneousIdealQuotientGrading.coeAddMonoidHom_map_pieceHom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.coeAddMonoidHom_map_pieceHom

/--
info: 'HomogeneousIdealQuotientGrading.preDecompose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.preDecompose

/--
info: 'HomogeneousIdealQuotientGrading.preDecompose_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.preDecompose_apply

/--
info: 'HomogeneousIdealQuotientGrading.preDecompose_apply_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.preDecompose_apply_apply

/--
info: 'HomogeneousIdealQuotientGrading.preDecompose_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.preDecompose_of_mem

/--
info: 'HomogeneousIdealQuotientGrading.coeAddMonoidHom_preDecompose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.coeAddMonoidHom_preDecompose

/--
info: 'HomogeneousIdealQuotientGrading.preDecompose_eq_zero_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.preDecompose_eq_zero_of_mem

/--
info: 'HomogeneousIdealQuotientGrading.quotDecompose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotDecompose

/--
info: 'HomogeneousIdealQuotientGrading.quotDecompose_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotDecompose_mk

/--
info: 'HomogeneousIdealQuotientGrading.decompositionOfImages' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.decompositionOfImages

/--
info: 'HomogeneousIdealQuotientGrading.gradedRingOfImages' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gradedRingOfImages

/--
info: 'HomogeneousIdealQuotientGrading.decompose_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.decompose_mk

/--
info: 'HomogeneousIdealQuotientGrading.decompose_mk_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.decompose_mk_apply

/--
info: 'HomogeneousIdealQuotientGrading.quotGrading' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotGrading

/--
info: 'HomogeneousIdealQuotientGrading.mem_quotGrading_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.mem_quotGrading_iff

/--
info: 'HomogeneousIdealQuotientGrading.mk_mem_quotGrading' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.mk_mem_quotGrading

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingPieceHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotGradingPieceHom

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingPieceHom_coe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotGradingPieceHom_coe

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingPieceHom_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotGradingPieceHom_surjective

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingGradedMonoid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotGradingGradedMonoid

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingGradedRing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotGradingGradedRing

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingGradedRingOfHomogeneous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotGradingGradedRingOfHomogeneous

/--
info: 'HomogeneousIdealQuotientGrading.decompose_quotGrading_mk_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.decompose_quotGrading_mk_apply

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotGradingSubmodule

/--
info: 'HomogeneousIdealQuotientGrading.mem_quotGradingSubmodule_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.mem_quotGradingSubmodule_iff

/--
info: 'HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebra

/--
info: 'HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebraOfHomogeneous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebraOfHomogeneous

/--
info: 'HomogeneousIdealQuotientGrading.decompose_quotGradingSubmodule_mk_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.decompose_quotGradingSubmodule_mk_apply

/--
info: 'HomogeneousIdealQuotientGrading.gateIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gateIdeal

/--
info: 'HomogeneousIdealQuotientGrading.gateIdeal_isHomogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gateIdeal_isHomogeneous

/--
info: 'HomogeneousIdealQuotientGrading.gateHomogeneousIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gateHomogeneousIdeal

/--
info: 'HomogeneousIdealQuotientGrading.gate_gateIdeal_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gate_gateIdeal_ne_bot

/--
info: 'HomogeneousIdealQuotientGrading.gate_mk_X0X1_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gate_mk_X0X1_eq_zero

/--
info: 'HomogeneousIdealQuotientGrading.gate_X0_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gate_X0_not_mem

/--
info: 'HomogeneousIdealQuotientGrading.gate_mk_X0_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gate_mk_X0_ne_zero

/--
info: 'HomogeneousIdealQuotientGrading.gate_mk_X0_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gate_mk_X0_mem

/--
info: 'HomogeneousIdealQuotientGrading.gateGradedRing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gateGradedRing

/--
info: 'HomogeneousIdealQuotientGrading.gateGradedAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gateGradedAlgebra

/--
info: 'HomogeneousIdealQuotientGrading.gate_decompose_mk_X0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomogeneousIdealQuotientGrading.gate_decompose_mk_X0
