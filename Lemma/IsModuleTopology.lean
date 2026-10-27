import Mathlib
import Instance.Mathlib_IsModuleTopology
import Class.Mathlib_IsModuleTopology
import Def.IsModuleTopology
import Theorem.IsModuleTopology


section

section linear

variable {A B : Type*} (S' : Type*) {S : Type*}
    [Semiring S'] [Semiring S] [AddCommMonoid A] [AddCommMonoid B] [Module S A]
    [Module S B] [Module S' A] [Module S' B]

theorem LinearMap.changeScalars_apply (f : A →ₗ[S] B) [IsBiscalar S S' f] (a : A) :
    LinearMap.changeScalars S' f a = f a := by
  simp [changeScalars]

end linear

section algebra

variable {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S] [Algebra S A]
    [Algebra S B] [Algebra S' A] [Algebra S' B]

theorem AlgHom.changeScalars_apply (f : A →ₐ[S] B) [IsBiscalar S S' f] (a : A) :
    changeScalars S' f a = f a := by
  simp [changeScalars]

end algebra

end

section

theorem ModuleTopology.isModuleTopology (R : Type*) [TopologicalSpace R] (S : Type*) [Add S]
    [SMul R S] : @IsModuleTopology R _ S _ _ (moduleTopology R S) where
  __ := moduleTopology R S
  eq_moduleTopology' := rfl

lemma ModuleTopology.iff (R M : Type*) [Add M] [SMul R M] [TopologicalSpace R]
    [τ : TopologicalSpace M] : IsModuleTopology R M ↔ τ = moduleTopology R M :=
  ⟨fun m ↦ m.eq_moduleTopology', fun a ↦ { eq_moduleTopology' := a }⟩

namespace IsModuleTopology

open ModuleTopology

section semiring_bilinear

variable {R : Type*} [τR : TopologicalSpace R] [CommSemiring R]

variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]
variable {C : Type*} [AddCommMonoid C] [Module R C] [aC : TopologicalSpace C] [IsModuleTopology R C]

theorem Module.continuous_bilinear_of_finite_free [IsTopologicalSemiring R] [Module.Finite R A]
    [Module.Free R A] (bil : A →ₗ[R] B →ₗ[R] C) :
    Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  let ι := Module.Free.ChooseBasisIndex R A
  let hι : Fintype ι := Module.Free.ChooseBasisIndex.fintype R A
  let b : Module.Basis ι R A := Module.Free.chooseBasis R A
  let elinear : A ≃ₗ[R] (ι → R) := b.equivFun
  let bil' : (ι → R) →ₗ[R] B →ₗ[R] C := bil.comp elinear.symm.toLinearMap
  have := continuous_bilinear_of_pi_fintype ι bil'
  have foo : (fun ab ↦ (bil ab.1) ab.2 : A × B → C) = (fun fb ↦ bil' fb.1 fb.2) ∘
    (fun ab ↦ (elinear ab.1, ab.2) : A × B → (ι → R) × B) := by
    ext ⟨a, b⟩
    simp [bil']
  rw [foo]
  apply Continuous.comp this
  apply Continuous.prodMk
  · exact continuous_of_linearMap (elinear.toLinearMap ∘ₗ (LinearMap.fst R A B))
  · fun_prop

end semiring_bilinear

section semiring_algebra

open scoped TensorProduct

variable (R) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]
variable [TopologicalSpace D] [IsModuleTopology R D]

include R in
lemma topologicalSemiring : IsTopologicalSemiring D where
  continuous_add := (toContinuousAdd R D).1
  continuous_mul := continuous_mul' R D

end semiring_algebra

section ring_algebra

variable (R) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]
variable [TopologicalSpace D] [IsModuleTopology R D]

include R in
lemma Module.topologicalRing : IsTopologicalRing D where
  continuous_add := (toContinuousAdd R D).1
  continuous_mul := continuous_mul R D
  continuous_neg := continuous_neg R D

end ring_algebra

section algebra

variable (R S : Type*)
  [CommRing R] [TopologicalSpace R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]

lemma iff_Continuous_algebraMap :
    IsTopologicalModule R S ↔ Continuous (algebraMap R S) := by
  refine ⟨fun _ ↦ continuous_algebraMap R S, fun h ↦ ?_⟩
  have : Continuous (fun rs ↦ algebraMap R S rs.1 • rs.2 : R × S → S) := by fun_prop
  simp_rw [← algebra_compatible_smul S] at this
  have : ContinuousSMul R S := ⟨this⟩
  exact IsTopologicalModule.mk

end algebra

section trans

variable (R : Type*) [CommRing R] [TopologicalSpace R]

theorem isTopologicalModule
    (M : Type*) [AddCommGroup M] [TopologicalSpace M] [Module R M]
    [IsModuleTopology R M] : IsTopologicalModule R M where
      continuous_smul := eq_moduleTopology R M ▸ (continuousSMul R M).1
      continuous_add := eq_moduleTopology R M ▸ (continuousAdd R M).1

variable (S : Type*) [CommRing S] [TopologicalSpace S] [Algebra R S]

variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

lemma _root_.Algebra.moduleTopology_le [IsTopologicalModule R S] :
    moduleTopology R M ≤ moduleTopology S M := by
  letI : TopologicalSpace M := moduleTopology S M
  haveI : ContinuousAdd M := continuousAdd S M
  have ⟨cts_smul⟩ : ContinuousSMul S M := continuousSMul S M
  suffices ContinuousSMul R M from _root_.moduleTopology_le R M
  constructor
  suffices Continuous (fun rm ↦ algebraMap R S rm.1 • rm.2 : R × M → M) by
    simpa [← algebra_compatible_smul S]
  fun_prop

lemma _root_.moduleTopology.trans [IsTopologicalRing R] [Module.Finite R S] [IsModuleTopology R S] :
    moduleTopology R M = moduleTopology S M := by
  have := IsModuleTopology.isTopologicalModule
  refine le_antisymm (Algebra.moduleTopology_le _ _ _) ?_
  letI : TopologicalSpace M := moduleTopology R M
  haveI : IsModuleTopology R M := isModuleTopology R M
  haveI : ContinuousAdd M := continuousAdd R M
  have ⟨cts_smul⟩ : ContinuousSMul R M := continuousSMul R M
  suffices ContinuousSMul S M from _root_.moduleTopology_le S M
  constructor
  let bil : S →ₗ[R] M →ₗ[R] M := {
    toFun s := {
      toFun m := s • m
      map_add' := DistribSMul.smul_add s
      map_smul' := smul_comm s
    }
    map_add' s t := by
      ext m
      exact Module.add_smul s t m
    map_smul' r s := by
      ext m
      exact IsScalarTower.smul_assoc r s m
  }
  exact continuous_bilinear_of_finite_left bil

lemma trans [IsTopologicalRing R] [Module.Finite R S] [IsModuleTopology R S]
    [τ : TopologicalSpace M] :
    IsModuleTopology R M ↔ IsModuleTopology S M := by
  simp [iff R M, iff S M, moduleTopology.trans R S]

end trans

section opensubring
variable (R S : Type*)
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra R S]

open scoped Topology in

theorem of_continuous_isOpenMap_algebraMap (hcont : Continuous (algebraMap R S))
    (hopen : IsOpenMap (algebraMap R S)) : IsModuleTopology R S where
  eq_moduleTopology' := by

    have : ContinuousSMul R S := continuousSMul_of_algebraMap R S hcont

    have hcont_id : Continuous[moduleTopology R S, _] id :=
      continuous_id_iff_le.2 <| moduleTopology_le _ _

    have hcont_alg : Continuous[_, moduleTopology R S] (Algebra.linearMap R S) :=

      letI := moduleTopology R S
      letI : ContinuousAdd S := ModuleTopology.continuousAdd _ _
      letI : ContinuousSMul R S := ModuleTopology.continuousSMul _ _
      IsModuleTopology.continuous_of_linearMap _

    have hopen_mpr {U : Set S} (h : IsOpen U) : IsOpen[moduleTopology R S] U :=
      @Continuous.isOpen_preimage S S (moduleTopology R S) _ id hcont_id U h

    have hopen_mp {U : Set S} (h : IsOpen[moduleTopology R S] U)
        (hUS : U ⊆ Set.range (algebraMap R S)) : IsOpen U :=
      Set.image_preimage_eq_of_subset hUS ▸ hopen _ <|
        @Continuous.isOpen_preimage R S _ (moduleTopology R S) _ hcont_alg U h

    rw [IsTopologicalRing.to_topologicalAddGroup.ext_iff <|

      @IsModuleTopology.topologicalAddGroup R _ _ S _ _ (moduleTopology R S) (isModuleTopology R S)]

    apply (nhds_basis_opens 0).ext (@nhds_basis_opens S (moduleTopology R S) 0)
    ·
      exact fun U hU => ⟨U, ⟨⟨hU.1, hopen_mpr hU.2⟩, by simp⟩⟩
    ·
      intro U hU

      refine ⟨Set.range (algebraMap R S) ∩ U, ⟨⟨⟨⟨0, by simp⟩, hU.1⟩, ?_⟩, by simp⟩⟩

      let hopen_range := hopen_mpr hopen.isOpen_range

      exact hopen_mp (@IsOpen.inter _ (moduleTopology R S) _ _ hopen_range hU.2) (by simp)

end opensubring

section quotientMap

variable {R M : Type*} [Ring R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  (N : Type*) [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsModuleTopology R N]

theorem of_isQuotientMap (f : N →ₗ[R] M) (h : Topology.IsQuotientMap f) : IsModuleTopology R M := by
  rw [iff, eq_coinduced_of_surjective h.surjective, h.eq_coinduced]

variable [ContinuousAdd M] [ContinuousSMul R M]

theorem of_isOpenMap_surjective (f : N →ₗ[R] M) (h : IsOpenMap f) (hsurj : Function.Surjective f)
    : IsModuleTopology R M := by
  apply of_isQuotientMap N f
  refine IsOpenQuotientMap.isQuotientMap ⟨hsurj, continuous_of_linearMap f, h⟩

theorem of_inverse (f : N →ₗ[R] M) (g : M → N) (hc : Continuous g) (hi : Function.LeftInverse f g)
    : IsModuleTopology R M := by
  apply of_isQuotientMap N f
  exact Topology.IsQuotientMap.of_inverse hc (continuous_of_linearMap f) hi

end quotientMap

theorem t2Space (R : Type*) {M : Type*} [Semiring R] [AddCommGroup M] [Module R M] [Module.Free R M]
    [TopologicalSpace R] [TopologicalSpace M] [T2Space R]
    [ContinuousAdd R] [ContinuousMul R] [IsModuleTopology R M]
    : T2Space M := by
  have := IsModuleTopology.topologicalAddGroup R M
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
  let f := (Module.Free.chooseBasis R M).repr |>.toLinearMap
  let g : (Module.Free.ChooseBasisIndex R M →₀ R) →ₗ[R] (Module.Free.ChooseBasisIndex R M → R) := {
    __ := Finsupp.coeFnAddHom
    map_smul' _ _ := rfl
  }
  suffices hpre : (g.comp f) ⁻¹' {0} = {0}  by
    rw [← hpre]
    apply IsClosed.preimage <| IsModuleTopology.continuous_of_linearMap (g.comp f)
    exact isClosed_singleton
  ext x
  simp [map_eq_zero_iff g DFunLike.coe_injective,
    map_eq_zero_iff f (Module.Free.chooseBasis R M).repr.injective]

theorem t2Space' {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [TopologicalSpace K] [TopologicalSpace V] [T2Space K]
    [ContinuousAdd K] [ContinuousMul K] [mt : IsModuleTopology K V]
    : T2Space V := by
  apply t2Space (R := K)

section locally_compact

variable (R : Type*) [τR : TopologicalSpace R] [Ring R] [IsTopologicalRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]

theorem locallyCompactSpaceOfFinite [LocallyCompactSpace R] [Module.Finite R M] :
    LocallyCompactSpace M := by

  obtain ⟨n, φ, h⟩ := Module.Finite.exists_fin (R := R) (M := M)

  exact IsOpenQuotientMap.locallyCompactSpace <|

    AddMonoidHom.isOpenQuotientMap_of_isQuotientMap <|

    isQuotientMap_of_surjective <|
    LinearMap.range_eq_top.mp <|
    h ▸ Fintype.range_linearCombination R φ

end locally_compact

section SecondCountableTopology

lemma _root_.Module.Finite.secondCountabletopology (R M : Type*)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [TopologicalSpace M]
    [IsModuleTopology R M] : SecondCountableTopology M := by
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R M
  have := isQuotientMap_of_surjective hφ
  apply Topology.IsQuotientMap.secondCountableTopology <| isQuotientMap_of_surjective hφ
  exact isOpenMap_of_surjective hφ

end SecondCountableTopology

end IsModuleTopology

end
