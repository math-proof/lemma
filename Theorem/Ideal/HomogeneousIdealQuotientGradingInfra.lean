module

public import Mathlib
public import Instance.AlgebraicGeometry_HomogeneousIdealQuotientGradingInfra

public section

namespace HomogeneousIdealQuotientGrading

open DirectSum

section Engine

variable {ι A σ τ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
variable (I : Ideal A)
variable [SetLike τ (A ⧸ I)] [AddSubmonoidClass τ (A ⧸ I)] (ℬ : ι → τ)


@[simp] public theorem pieceHom_coe (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (i : ι) (a : 𝒜 i) :
    (pieceHom 𝒜 I ℬ hmem i a : A ⧸ I) = Ideal.Quotient.mk I (a : A) := rfl


public theorem pieceHom_surjective (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b) (i : ι) :
    Function.Surjective (pieceHom 𝒜 I ℬ hmem i) := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha, rfl⟩ := hsurj i b hb
  exact ⟨⟨a, ha⟩, rfl⟩

omit [AddSubmonoidClass σ A] [AddSubmonoidClass τ (A ⧸ I)] in


public theorem gradedMonoidOfImages [AddMonoid ι] [SetLike.GradedMonoid 𝒜]
    (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b) :
    SetLike.GradedMonoid ℬ where
  one_mem := by
    have h1 : (1 : A ⧸ I) = Ideal.Quotient.mk I 1 := (map_one _).symm
    rw [h1]
    exact hmem 0 1 (SetLike.one_mem_graded 𝒜)
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨a, ha, rfl⟩ := hsurj i x hx
    obtain ⟨b, hb, rfl⟩ := hsurj j y hy
    rw [← map_mul]
    exact hmem _ _ (SetLike.mul_mem_graded ha hb)

variable [DecidableEq ι]


public theorem coeAddMonoidHom_map_pieceHom
    (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (y : ⨁ i, 𝒜 i) :
    DirectSum.coeAddMonoidHom ℬ (DirectSum.map (pieceHom 𝒜 I ℬ hmem) y)
      = Ideal.Quotient.mk I (DirectSum.coeAddMonoidHom 𝒜 y) := by
  refine DirectSum.induction_on y ?_ ?_ ?_
  · simp
  · intro i x
    rw [DirectSum.map_of, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of,
      pieceHom_coe]
  · intro x y hx hy
    rw [map_add, map_add, map_add, map_add, hx, hy]

variable [AddMonoid ι] [GradedRing 𝒜]


public theorem preDecompose_apply (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (a : A) :
    preDecompose 𝒜 I ℬ hmem a = DirectSum.map (pieceHom 𝒜 I ℬ hmem) (decompose 𝒜 a) := rfl


public theorem preDecompose_apply_apply
    (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) (i : ι) :
    preDecompose 𝒜 I ℬ hmem a i = pieceHom 𝒜 I ℬ hmem i (decompose 𝒜 a i) := by
  rw [preDecompose_apply, DirectSum.map_apply]


public theorem preDecompose_of_mem (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    preDecompose 𝒜 I ℬ hmem a
      = DirectSum.of (fun j => ℬ j) i ⟨Ideal.Quotient.mk I a, hmem i a ha⟩ := by
  rw [preDecompose_apply, decompose_of_mem 𝒜 ha, DirectSum.map_of]
  rfl


public theorem coeAddMonoidHom_preDecompose
    (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) :
    DirectSum.coeAddMonoidHom ℬ (preDecompose 𝒜 I ℬ hmem a) = Ideal.Quotient.mk I a := by
  rw [preDecompose_apply, coeAddMonoidHom_map_pieceHom]
  congr 1
  exact (DirectSum.decompose 𝒜).symm_apply_apply a


public theorem preDecompose_eq_zero_of_mem
    (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (hI : I.IsHomogeneous 𝒜) {a : A} (ha : a ∈ I) :
    preDecompose 𝒜 I ℬ hmem a = 0 := by
  ext i
  rw [preDecompose_apply_apply, DirectSum.zero_apply, pieceHom_coe, ZeroMemClass.coe_zero,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hI i ha


@[simp] public theorem quotDecompose_mk
    (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (hI : I.IsHomogeneous 𝒜) (a : A) :
    quotDecompose 𝒜 I ℬ hmem hI (Ideal.Quotient.mk I a) = preDecompose 𝒜 I ℬ hmem a := rfl


public theorem decompose_mk (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    [DirectSum.Decomposition ℬ] (a : A) :
    DirectSum.decompose ℬ (Ideal.Quotient.mk I a)
      = DirectSum.map (pieceHom 𝒜 I ℬ hmem) (DirectSum.decompose 𝒜 a) := by
  apply (DirectSum.decompose ℬ).symm.injective
  rw [Equiv.symm_apply_apply]
  rw [show ⇑(DirectSum.decompose ℬ).symm = ⇑(DirectSum.coeAddMonoidHom ℬ) from rfl]
  rw [coeAddMonoidHom_map_pieceHom]
  congr 1
  exact ((DirectSum.decompose 𝒜).symm_apply_apply a).symm


public theorem decompose_mk_apply (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    [DirectSum.Decomposition ℬ] (a : A) (i : ι) :
    (DirectSum.decompose ℬ (Ideal.Quotient.mk I a) i : A ⧸ I)
      = Ideal.Quotient.mk I (DirectSum.decompose 𝒜 a i) := by
  rw [decompose_mk 𝒜 I ℬ hmem, DirectSum.map_apply, pieceHom_coe]

end Engine

section QuotGradingDef

variable {ι A σ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ)
variable (I : Ideal A)


public theorem mem_quotGrading_iff {i : ι} {x : A ⧸ I} :
    x ∈ quotGrading 𝒜 I i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩


public theorem mk_mem_quotGrading {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    Ideal.Quotient.mk I a ∈ quotGrading 𝒜 I i :=
  (mem_quotGrading_iff 𝒜 I).mpr ⟨a, ha, rfl⟩


@[simp] public theorem quotGradingPieceHom_coe (i : ι) (a : 𝒜 i) :
    (quotGradingPieceHom 𝒜 I i a : A ⧸ I) = Ideal.Quotient.mk I (a : A) := rfl


public theorem quotGradingPieceHom_surjective (i : ι) :
    Function.Surjective (quotGradingPieceHom 𝒜 I i) :=
  pieceHom_surjective 𝒜 I (quotGrading 𝒜 I) (fun _ _ ha => mk_mem_quotGrading 𝒜 I ha)
    (fun _ _ hb => (mem_quotGrading_iff 𝒜 I).mp hb) i

end QuotGradingDef

section QuotGradingGraded

variable {ι A σ : Type*}
variable [DecidableEq ι] [AddMonoid ι] [CommRing A]
variable [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
variable (I : Ideal A)


public theorem decompose_quotGrading_mk_apply (J : HomogeneousIdeal 𝒜) (a : A) (i : ι) :
    (DirectSum.decompose (quotGrading 𝒜 J.toIdeal) (Ideal.Quotient.mk J.toIdeal a) i
        : A ⧸ J.toIdeal)
      = Ideal.Quotient.mk J.toIdeal (DirectSum.decompose 𝒜 a i) :=
  decompose_mk_apply 𝒜 J.toIdeal (quotGrading 𝒜 J.toIdeal)
    (fun _ _ ha => mk_mem_quotGrading 𝒜 J.toIdeal ha) a i

end QuotGradingGraded

section SubmoduleVersion

variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A)
variable (I : Ideal A)


public theorem mem_quotGradingSubmodule_iff {i : ι} {x : A ⧸ I} :
    x ∈ quotGradingSubmodule 𝒜 I i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩


public theorem mk_mem_quotGradingSubmodule {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    Ideal.Quotient.mk I a ∈ quotGradingSubmodule 𝒜 I i :=
  (mem_quotGradingSubmodule_iff 𝒜 I).mpr ⟨a, ha, rfl⟩

variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]


public theorem decompose_quotGradingSubmodule_mk_apply (J : HomogeneousIdeal 𝒜) (a : A) (i : ι) :
    (DirectSum.decompose (quotGradingSubmodule 𝒜 J.toIdeal) (Ideal.Quotient.mk J.toIdeal a) i
        : A ⧸ J.toIdeal)
      = Ideal.Quotient.mk J.toIdeal (DirectSum.decompose 𝒜 a i) :=
  decompose_mk_apply 𝒜 J.toIdeal (quotGradingSubmodule 𝒜 J.toIdeal)
    (fun _ _ ha => mk_mem_quotGradingSubmodule 𝒜 J.toIdeal ha) a i

end SubmoduleVersion

section Gate

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra


public theorem gateIdeal_isHomogeneous :
    (gateIdeal).IsHomogeneous (homogeneousSubmodule (Fin 2) ℤ) := by
  refine Ideal.homogeneous_span _ _ ?_
  rintro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact ⟨2, (mem_homogeneousSubmodule _ _).mpr ((isHomogeneous_X _ _).mul (isHomogeneous_X _ _))⟩


public theorem gate_gateIdeal_ne_bot : gateIdeal ≠ ⊥ := by
  intro h
  have hmem : (X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ∈ gateIdeal :=
    Ideal.mem_span_singleton_self _
  rw [h, Ideal.mem_bot] at hmem
  exact mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _) hmem


public theorem gate_mk_X0X1_eq_zero :
    Ideal.Quotient.mk gateIdeal (X 0 * X 1 : MvPolynomial (Fin 2) ℤ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)


public theorem gate_X0_not_mem : (X 0 : MvPolynomial (Fin 2) ℤ) ∉ gateIdeal := by
  intro h
  rw [gateIdeal, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have := congrArg (MvPolynomial.eval (fun j : Fin 2 => if j = 0 then (1 : ℤ) else 0)) hc
  simp [MvPolynomial.eval_X, MvPolynomial.eval_mul] at this


public theorem gate_mk_X0_ne_zero :
    Ideal.Quotient.mk gateIdeal (X 0 : MvPolynomial (Fin 2) ℤ) ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact gate_X0_not_mem


public theorem gate_mk_X0_mem :
    Ideal.Quotient.mk gateIdeal (X 0 : MvPolynomial (Fin 2) ℤ)
      ∈ quotGrading (homogeneousSubmodule (Fin 2) ℤ) gateIdeal 1 :=
  mk_mem_quotGrading _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ _))


public theorem gate_decompose_mk_X0 :
    (DirectSum.decompose (quotGrading (homogeneousSubmodule (Fin 2) ℤ) gateHomogeneousIdeal.toIdeal)
        (Ideal.Quotient.mk gateHomogeneousIdeal.toIdeal (X 0 : MvPolynomial (Fin 2) ℤ)) 1
      : MvPolynomial (Fin 2) ℤ ⧸ gateHomogeneousIdeal.toIdeal)
      = Ideal.Quotient.mk gateHomogeneousIdeal.toIdeal (X 0 : MvPolynomial (Fin 2) ℤ) := by
  rw [decompose_quotGrading_mk_apply]
  congr 1
  have hX : (X 0 : MvPolynomial (Fin 2) ℤ) ∈ homogeneousSubmodule (Fin 2) ℤ 1 :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ _)
  exact DirectSum.decompose_of_mem_same _ hX

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
