-- Carved from Lemma/Definitions/Def_Deformations_Deformations_Lemmas.lean: instance decls only.
import Mathlib


instance {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G] :
    MulAction α (M →* G) where
  smul a f := ⟨⟨a • f, by simp⟩, by simp⟩
  one_smul _ := by ext; exact one_smul _ _
  mul_smul a b f := by ext x; change (a * b) • (f x) = a • b • (f x); simp [mul_smul]


instance {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    [TopologicalSpace M] [TopologicalSpace G] [ContinuousConstSMul α G] :
    MulAction α (M →ₜ* G) where
  smul a f := ⟨a • f, .const_smul f.2 _⟩
  one_smul _ := by ext; exact one_smul _ _
  mul_smul a b f := by ext x; change (a * b) • (f x) = a • b • (f x); simp [mul_smul]


instance {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] :
    ContinuousConstSMul (ConjAct G) G :=
  ⟨fun _ ↦ .mul (continuous_const.mul continuous_id) continuous_const⟩

@[to_additive]
instance IsTopologicalGroup.discreteUniformity
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] :
    letI := IsTopologicalGroup.rightUniformSpace G
    DiscreteUniformity G := by
  simp only [discreteUniformity_iff_setRelId_mem_uniformity]
  exact ⟨{1}, by simp [Set.subset_def, ← div_eq_mul_inv, div_eq_one]⟩


instance ContinuousAlgHom.isLocalHom_id {R A : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A] :
    IsLocalHom (ContinuousAlgHom.id R A) := by
  convert isLocalHom_id A
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩


instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A →A[R] B) [IsLocalHom f] : IsLocalHom f.toRingHom := by
  rwa [ContinuousAlgHom.isLocalHom_toRingHom]

instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A ≃A[R] B) : IsLocalHom (f : A →A[R] B) := by
  convert isLocalHom_equiv f
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A →A[R] B) [IsLocalHom f] : IsLocalHom f.toRingHom := by
  rwa [ContinuousAlgHom.isLocalHom_toRingHom]

instance {A B : Type*} [Semiring A] [Semiring B]
    (F : Type*) [EquivLike F A B] [RingEquivClass F A B] (f : F) :
    IsLocalHom (RingHomClass.toRingHom f) := by
  convert isLocalHom_equiv f
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

instance {R S} [Semiring R] [Semiring S] (e : R ≃+* S) : IsLocalHom e.toRingHom :=
  ⟨fun x hx ↦ by convert hx.map e.symm; simp⟩

instance ContinuousAlgHom.isLocalHom_comp {R A B C : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {g : B →A[R] C} {f : A →A[R] B}
    [IsLocalHom g] [IsLocalHom f] :
    IsLocalHom (g.comp f) := by
  convert RingHom.isLocalHom_comp g.toRingHom f.toRingHom
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

instance {R : Type*} [CommSemiring R] : IsLocalHom (algebraMap R R) :=
  isLocalHom_id R

open IsLocalRing in
instance {R : Type*} [CommRing R] [IsLocalRing R] :
    IsLocalHom (algebraMap R (ResidueField R)) :=
  IsLocalRing.instIsLocalHomResidueFieldRingHomResidue _

noncomputable


instance {A n m : Type*} [CommRing A] [TopologicalSpace A]
    [Finite n] [Finite m] [IsTopologicalRing A] :
    IsModuleTopology A (Matrix n m A) := IsModuleTopology.instPi


instance {G K L : Type*} [Field K] [Field L] [Algebra K L] [Monoid G] [MulSemiringAction G L]
    [SMulCommClass G K L]
    (E : IntermediateField K L) [Normal K E] : MulSemiringAction G E where
  smul σ x := ⟨σ • x, by
    convert ((MulSemiringAction.toAlgHom K L σ).restrictNormal E x).2
    exact ((MulSemiringAction.toAlgHom K L σ).restrictNormal_commutes E x).symm⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)

open NumberField in
instance {G K : Type*} [Field K] [Monoid G] [MulSemiringAction G K] :
    MulSemiringAction G (𝓞 K) where
  smul σ x := ⟨σ • x, x.2.map (MulSemiringAction.toAlgHom ℤ K σ)⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)


instance {K A : Type*} [Field K] [CommRing A] [Algebra K A] (R : ValuationSubring K)
    [FaithfulSMul K A] : FaithfulSMul R A :=
  Subsemiring.instFaithfulSMulSubtypeMem R

instance {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K]
    (E : IntermediateField K L) [FiniteDimensional K E] : NumberField E where
  to_finiteDimensional := .trans ℚ K E

instance IntermediateField.smulCommClass_of_normal
    {K L G : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)
    [Monoid G] [MulSemiringAction G L] [SMulCommClass G K L] [Normal K E] :
    SMulCommClass G K E where
  smul_comm g k e := Subtype.ext <| smul_comm g k e.1

instance ValuationSubring.smulCommClass
    (K L G : Type*) [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L]
    [Monoid G] [MulSemiringAction G L] [SMulCommClass G K L] :
    SMulCommClass G O L where
  smul_comm g o l := smul_comm g o.1 l


instance {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    H.op.FiniteIndex := ⟨by rw [Subgroup.index_op]; exact Subgroup.FiniteIndex.index_ne_zero⟩

instance Additive.instDistrbMulAction
    {G M : Type*} [Monoid G] [Monoid M] [MulDistribMulAction G M] :
    DistribMulAction G (Additive M) where
  smul g m := .ofMul (g • m.toMul)
  one_smul m := one_smul _ m.toMul
  mul_smul g h m := mul_smul g h m.toMul
  smul_zero g := smul_one (N := M) g
  smul_add g m n := MulDistribMulAction.smul_mul g m.toMul n.toMul
