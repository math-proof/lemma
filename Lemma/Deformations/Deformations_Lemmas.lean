import Mathlib
import Lemma.AlgebraicCurve.PlaceCompletion
import Def.Deformations_Deformations_Lemmas

lemma IsLinearTopology.exists_ideal_isMaximal_and_isOpen
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] [Nontrivial R] [T0Space R] :
    ∃ I : Ideal R, I.IsMaximal ∧ IsOpen (X := R) I := by
  obtain ⟨I, hI, hI'⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp
    ((isClosed_singleton (x := (1 : R))).isOpen_compl.mem_nhds (x := 0) (by simp))
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I (by simpa [Ideal.eq_top_iff_one] using hI')
  exact ⟨J, hJ, AddSubgroup.isOpen_mono (H₁ := I.toAddSubgroup) (H₂ := J.toAddSubgroup) hIJ hI⟩


@[simp]
lemma ContinuousAlgHom.coe_toContinuousMonoidHom
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B) :
    (f.toContinuousMonoidHom : A → B) = f := rfl

lemma MonoidHom.coe_smul
    {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    (a : α) (f : M →* G) :
    ⇑(a • f) = a • ⇑f := rfl

lemma ContinuousMonoidHom.coe_smul
    {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    [TopologicalSpace M] [TopologicalSpace G] [ContinuousConstSMul α G]
    (a : α) (f : M →ₜ* G) :
    ⇑(a • f) = a • ⇑f := rfl


lemma IsLocalRing.ResidueField.map_surjective {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (H : Function.Surjective f) :
    Function.Surjective (IsLocalRing.ResidueField.map f) :=
  Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.mk_surjective.comp H)

open Topology in
@[to_additive]
lemma MonoidHom.continuous_iff_isOpen_ker {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [Group α] [MulOneClass β] {f : α →* β} [DiscreteTopology β] [IsTopologicalGroup α] :
    Continuous f ↔ IsOpen (X := α) f.ker := by
  refine ⟨fun H ↦ H.1 {1} (isOpen_discrete _), fun H ↦ continuous_of_continuousAt_one _ ?_⟩
  simpa [ContinuousAt] using Filter.eventually_of_mem (H.mem_nhds (by simp)) (by simp)

lemma RingHom.continuous_iff_isOpen_ker {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [Ring α] [Semiring β] {f : α →+* β} [DiscreteTopology β] [IsTopologicalAddGroup α] :
    Continuous f ↔ IsOpen (X := α) (RingHom.ker f) :=
  AddMonoidHom.continuous_iff_isOpen_ker (f := f.toAddMonoidHom)

open Topology in
lemma continuousAt_discrete_rng {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {x : α} [DiscreteTopology β] :
    ContinuousAt f x ↔ ∀ᶠ y in 𝓝 x, f y = f x := by
  simp [ContinuousAt]

nonrec

lemma ContinuousAlgHom.isLocalHom_toRingHom {R A B : Type*}
    [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B]
    [TopologicalSpace A] [TopologicalSpace B]
    {f : A →A[R] B} :
    IsLocalHom f.toRingHom ↔ IsLocalHom f :=
  ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩


lemma AlgebraicClosure.map_algebraMap {K L : Type*} [Field K] [Field L] (f : K →+* L) (x) :
    map f (algebraMap K _ x) = algebraMap _ _ (f x) :=
    letI := f.toAlgebra
    (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).commutes _

nonrec
lemma IsModuleTopology.continuous_det {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {M : Type*} [AddCommGroup M] [Module A M]
    [TopologicalSpace (Module.End A M)] [IsModuleTopology A (Module.End A M)] :
    Continuous (LinearMap.det : Module.End A M →* A) := by
  classical
  by_cases H : ∃ s : Finset M, Nonempty (Module.Basis s A M)
  · obtain ⟨s, ⟨b⟩⟩ := H
    have : IsModuleTopology A (Matrix s s A) := IsModuleTopology.instPi
    have : ContinuousAdd (Module.End A M) := IsModuleTopology.toContinuousAdd A _
    letI e : Module.End A M ≃A[A] Matrix s s A :=
    { __ := algEquivMatrix b,
      continuous_toFun := continuous_of_linearMap (algEquivMatrix b).toLinearMap,
      continuous_invFun := continuous_of_linearMap (algEquivMatrix b).symm.toLinearMap }
    rw [e.symm.isQuotientMap.continuous_iff]
    convert continuous_id.matrix_det (R := A) (n := s) using 1
    funext M
    exact LinearMap.det_toLin b M
  rw [LinearMap.det, dif_neg H]
  exact continuous_of_const fun x ↦ congrFun rfl


@[simp]
lemma ContinuousMonoidHom.mk_toMonoidHom {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M]
  [TopologicalSpace N] (f : M →* N) (hf : Continuous f) : (ContinuousMonoidHom.mk f hf) = f := rfl

@[simp]
lemma ContinuousMonoidHom.coe_mk {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M]
  [TopologicalSpace N] (f : M →* N) (hf : Continuous f) : ⇑(ContinuousMonoidHom.mk f hf) = f := rfl


lemma Subring.algebraMap_def {R : Type*} [CommRing R] (S : Subring R) :
    algebraMap S R = S.subtype := rfl


theorem Subgroup.index_op {G : Type*} [Group G] (H : Subgroup G) :
    H.op.index = H.index := by
  trans (H.comap (MulEquiv.inv' G).symm.toMonoidHom).index
  · congr 1
    ext; simp
  · exact Subgroup.index_comap_of_surjective _ (MulEquiv.inv' G).symm.surjective


lemma IsTopologicalGroup.totallyBounded {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ∀ s ∈ nhds (1 : G), ∃ H : Subgroup G, H.FiniteIndex ∧ ↑H ⊆ s) :
    letI := IsTopologicalGroup.rightUniformSpace G
    TotallyBounded (Set.univ : Set G) := by
  letI := IsTopologicalGroup.rightUniformSpace G
  rintro s ⟨t, ht1, hts⟩
  obtain ⟨H, hH, hHs⟩ := H _ ht1
  have : Finite (Gᵐᵒᵖ ⧸ H.op) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Set.range (MulOpposite.unop ∘ Quotient.out : Gᵐᵒᵖ ⧸ H.op → G),
    Set.finite_range _, fun x _ ↦
      Set.mem_iUnion₂_of_mem ⟨QuotientGroup.mk (.op x), rfl⟩ (hts (hHs ?_))⟩
  dsimp only
  rw [Function.comp_apply, SetLike.mem_coe, ← MulOpposite.unop_op (x⁻¹),
    ← MulOpposite.unop_mul, ← Subgroup.mem_op, MulOpposite.op_inv, ← QuotientGroup.eq]
  simp
