/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import sympy.atlas.v1.Atlas.NumberTheoryI.code.GroupCounts
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GroupCounts
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeberLocal2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ResidueFieldHelper
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.CyclotomicDVRInstances
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.FiniteDimension
import sympy.atlas.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra
import sympy.atlas.v1.Atlas.NumberTheoryI.code.KroneckerWeberLocal2
import sympy.atlas.v1.Atlas.NumberTheoryI.code.ResidueFieldHelper
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field

import Mathlib.RingTheory.RootsOfUnity.Lemmas
import sympy.atlas.v1.Atlas.NumberTheoryI.code.CyclotomicDVRInstances

noncomputable section

namespace KroneckerWeber

class IsAbelianExtension (F : Type*) (E : Type*) [Field F] [Field E]
    [Algebra F E] : Prop where
  isGalois : IsGalois F E
  comm : ∀ σ τ : (E ≃ₐ[F] E), σ * τ = τ * σ

class IsCyclicExtension (F : Type*) (E : Type*) [Field F] [Field E]
    [Algebra F E] : Prop where
  isGalois : IsGalois F E
  isCyclic : IsCyclic (E ≃ₐ[F] E)

def LiesInCyclotomicExtension (F : Type*) (K : Type*) [Field F] [Field K]
    [Algebra F K] : Prop :=
  ∃ (m : ℕ) (_ : m ≥ 1), Nonempty (K →ₐ[F] CyclotomicField m F)

instance IsAbelianExtension.toIsGalois (F E : Type*) [Field F] [Field E]
    [Algebra F E] [h : IsAbelianExtension F E] : IsGalois F E :=
  h.isGalois

def geom_sum_prod {R : Type*} [CommRing R] (ζ : R) (p : ℕ) : R :=
  ∏ k ∈ Finset.range (p - 1), ∑ i ∈ Finset.range (k + 1), ζ ^ i

noncomputable def projToLastTwo (p : ℕ) :
    Multiplicative (ZMod p × ZMod p × ZMod p) →* Multiplicative (ZMod p × ZMod p) where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd x).2
  map_one' := by simp [toAdd_one]
  map_mul' := by intro a b; simp [toAdd_mul, ofAdd_add]

lemma index_map_mulEquiv {G G' : Type*} [Group G] [Group G']
    (φ : G ≃* G') (H : Subgroup G) :
    (H.map φ.toMonoidHom).index = H.index := by
  apply Subgroup.index_map_eq
  · exact φ.surjective
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x = 1 := φ.injective (hx.trans (map_one φ).symm)
    rw [this]; exact H.one_mem

lemma index_subgroups_card_eq_of_mulEquiv {G G' : Type*} [Group G] [Group G']
    (φ : G ≃* G') (n : ℕ) :
    Nat.card {H : Subgroup G // H.index = n} =
      Nat.card {H : Subgroup G' // H.index = n} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv φ.mapSubgroup.toEquiv ?_
  intro H
  constructor
  · intro h
    change (φ.mapSubgroup H).index = n
    rw [show (φ.mapSubgroup H) = H.map φ.toMonoidHom from rfl]
    rw [index_map_mulEquiv]; exact h
  · intro h
    have : (φ.mapSubgroup H).index = n := h
    rw [show (φ.mapSubgroup H) = H.map φ.toMonoidHom from rfl] at this
    rw [index_map_mulEquiv] at this; exact this

theorem ps4_galois_index2_bound
    (K : Type) [Field K] [Algebra ℚ_[2] K]
    [FiniteDimensional ℚ_[2] K] [IsGalois ℚ_[2] K] :
    Nat.card {H : Subgroup (K ≃ₐ[ℚ_[2]] K) // H.index = 2} ≤ 7 := by
  rw [Nat.card_congr (KroneckerWeberLocal2.galoisCorrespondenceIndex ℚ_[2] K 2)]
  exact KroneckerWeberLocal2.ps4_at_most_7_quadratic_extensions K

theorem Z2Z4_index2_count :
    Nat.card {H : Subgroup (Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) //
      H.index = 2} = 15 :=
  GroupCounts.Z2Z4_index2_count

theorem lemma_20_11_no_Z2Z4 :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
      Nonempty ((K ≃ₐ[ℚ_[2]] K) ≃*
        Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) := by
  intro ⟨K, hK_field, hK_alg, hK_fd, hK_gal, ⟨φ⟩⟩
  have h_bound := ps4_galois_index2_bound K
  rw [index_subgroups_card_eq_of_mulEquiv φ 2, Z2Z4_index2_count] at h_bound
  omega

noncomputable def galoisCorrespondenceIndex (F : Type*) [Field F] (K : Type*) [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (n : ℕ) :
    {H : Subgroup (K ≃ₐ[F] K) // H.index = n} ≃
    {L : IntermediateField F K // Module.finrank F L = n} where
  toFun := fun ⟨H, hH⟩ => ⟨IntermediateField.fixedField H, by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
        @IntermediateField.fixingSubgroup_fixedField F _ K _ _ H _]
    exact hH⟩
  invFun := fun ⟨L, hL⟩ => ⟨L.fixingSubgroup, by
    rwa [← IntermediateField.finrank_eq_fixingSubgroup_index]⟩
  left_inv := fun ⟨H, _⟩ => by
    simp only [Subtype.mk.injEq]
    exact @IntermediateField.fixingSubgroup_fixedField F _ K _ _ H _
  right_inv := fun ⟨L, _⟩ => by
    simp only [Subtype.mk.injEq]
    exact IsGalois.fixedField_fixingSubgroup L

theorem ps5_galois_cyclic_quartic_bound
    (K : Type) [Field K] [Algebra ℚ_[2] K]
    [FiniteDimensional ℚ_[2] K] [IsGalois ℚ_[2] K] :
    Nat.card {H : Subgroup (K ≃ₐ[ℚ_[2]] K) //
      H.index = 4 ∧ ∃ (_ : H.Normal), IsCyclic ((K ≃ₐ[ℚ_[2]] K) ⧸ H)} ≤ 12 := by
  haveI : Finite (IntermediateField ℚ_[2] K) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ_[2] K
      (Field.exists_primitive_element ℚ_[2] K)
  apply le_trans _ (KroneckerWeberLocal2.ps5_at_most_12_cyclic_quartic_extensions K)
  apply Nat.card_le_card_of_injective
    (fun x => ⟨IntermediateField.fixedField x.1, by
      obtain ⟨H, hindex, hexists⟩ := x
      haveI : H.Normal := hexists.choose
      refine ⟨?_, ?_, ?_⟩
      · rw [IntermediateField.finrank_eq_fixingSubgroup_index,
            @IntermediateField.fixingSubgroup_fixedField ℚ_[2] _ K _ _ H _]
        exact hindex
      · exact IsGalois.of_fixedField_normal_subgroup H
      · exact (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient H)).mp hexists.choose_spec⟩)
  intro ⟨H1, _⟩ ⟨H2, _⟩ heq
  simp only [Subtype.mk.injEq] at heq ⊢
  have : (IntermediateField.fixedField H1).fixingSubgroup =
         (IntermediateField.fixedField H2).fixingSubgroup := by rw [heq]
  rwa [IntermediateField.fixingSubgroup_fixedField,
       IntermediateField.fixingSubgroup_fixedField] at this

theorem Z4Z3_cyclic_quartic_count_with_normal :
    Nat.card {H : Subgroup (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) //
      H.index = 4 ∧ ∃ (_ : H.Normal),
        IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)} = 28 := by
  rw [show (fun H : Subgroup (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) =>
      H.index = 4 ∧ ∃ (_ : H.Normal),
        IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)) =
    (fun H => H.index = 4 ∧
        IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)) from by
    ext H; constructor
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, Subgroup.normal_of_comm H, h2⟩]
  exact GroupCounts.Z4Z3_cyclic_quartic_count

theorem cyclic_normal_index_subgroups_card_eq_of_mulEquiv
    {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') (n : ℕ) :
    Nat.card {H : Subgroup G // H.index = n ∧ ∃ (_ : H.Normal), IsCyclic (G ⧸ H)} =
    Nat.card {H : Subgroup G' // H.index = n ∧ ∃ (_ : H.Normal), IsCyclic (G' ⧸ H)} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv φ.mapSubgroup.toEquiv ?_
  intro H
  constructor
  · rintro ⟨h_idx, h_norm, h_cyc⟩
    have h_norm' : (φ.mapSubgroup H).Normal := by
      change (H.map φ.toMonoidHom).Normal
      exact Subgroup.Normal.map h_norm φ.toMonoidHom φ.surjective
    refine ⟨?_, h_norm', ?_⟩
    · change (H.map (φ : G →* G')).index = n
      rw [Subgroup.index_map_equiv H φ]; exact h_idx
    · haveI : (H.map φ.toMonoidHom).Normal :=
        Subgroup.Normal.map h_norm φ.toMonoidHom φ.surjective
      haveI := h_norm
      exact (QuotientGroup.congr H (H.map φ.toMonoidHom) φ rfl).isCyclic.mp h_cyc

  · rintro ⟨h_idx, h_norm, h_cyc⟩
    have h_norm' : (φ.mapSubgroup H).Normal := h_norm
    haveI : (φ.mapSubgroup.toEquiv H).Normal := h_norm
    haveI : (H.map (φ : G →* G')).Normal := ‹_›
    have h_normH : H.Normal := by
      have heq : H = (H.map (φ : G →* G')).comap (φ : G →* G') := by
        ext x; constructor
        · intro hx; exact ⟨x, hx, rfl⟩
        · rintro ⟨y, hy, he⟩; exact φ.injective he ▸ hy
      rw [heq]; exact Subgroup.Normal.comap ‹(H.map (φ : G →* G')).Normal› _
    refine ⟨?_, h_normH, ?_⟩
    · change (H.map (φ : G →* G')).index = n at h_idx
      rw [Subgroup.index_map_equiv H φ] at h_idx; exact h_idx
    · haveI := h_normH
      haveI : (H.map φ.toMonoidHom).Normal := ‹(H.map (φ : G →* G')).Normal›
      exact (QuotientGroup.congr H (H.map φ.toMonoidHom) φ rfl).isCyclic.mpr h_cyc

theorem lemma_20_11_no_Z4Z3 :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
      Nonempty ((K ≃ₐ[ℚ_[2]] K) ≃*
        Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) := by
  intro ⟨K, hK_field, hK_alg, hK_fd, hK_gal, ⟨φ⟩⟩

  have h_bound := ps5_galois_cyclic_quartic_bound K

  rw [cyclic_normal_index_subgroups_card_eq_of_mulEquiv φ] at h_bound

  rw [Z4Z3_cyclic_quartic_count_with_normal] at h_bound

  omega

theorem lemma_20_11 :
    (¬ ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
      Nonempty ((K ≃ₐ[ℚ_[2]] K) ≃*
        Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2))) ∧
    (¬ ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
      Nonempty ((K ≃ₐ[ℚ_[2]] K) ≃*
        Multiplicative (ZMod 4 × ZMod 4 × ZMod 4))) :=
  ⟨lemma_20_11_no_Z2Z4, lemma_20_11_no_Z4Z3⟩

noncomputable def adicCompletionTensorLift
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    [IsScalarTower K (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    [IsScalarTower K L (𝔮.adicCompletion L)] :
    TensorProduct K (𝔭.adicCompletion K) L →ₐ[𝔭.adicCompletion K] 𝔮.adicCompletion L :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (𝔭.adicCompletion K) (𝔮.adicCompletion L))
    (IsScalarTower.toAlgHom K L (𝔮.adicCompletion L))
    (fun _ _ => mul_comm _ _)


section
set_option synthInstance.maxHeartbeats 400000
noncomputable def completion_residueFieldEquiv
    (A : Type u_A₈') [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K₈') [Field K] [Algebra A K] [IsFractionRing A K]
    (𝔭 : HeightOneSpectrum A) :
    (↥(𝔭.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) ≃+*
    (A ⧸ 𝔭.asIdeal) :=
  (RingHom.quotientKerEquivOfSurjective
    (𝔭.surj_completionResidueMap (K := K))).symm.trans
    (Ideal.quotEquivOfEq (𝔭.ker_completionResidueMap (K := K)))

set_option synthInstance.maxHeartbeats 400000 in
universe u_A₈c u_K₈c u_L₈c u_B₈c in
open IsDedekindDomain in
theorem isGalois_adicCompletion
    (A : Type u_A) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u_L) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type u_B) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [IsFractionRing B L]
    [𝔮.asIdeal.LiesOver 𝔭.asIdeal]
    (hgal : IsGalois K L) :
    letI := instAlgebraAdicCompletionOfLiesOver (L := L) K 𝔭 𝔮 h𝔮_over_𝔭
    IsGalois (𝔭.adicCompletion K) (𝔮.adicCompletion L) := by
  letI := instAlgebraAdicCompletionOfLiesOver (L := L) K 𝔭 𝔮 h𝔮_over_𝔭


  haveI : (Valued.v : Valuation (𝔭.adicCompletion K)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne Valued.v (e := 2) (by norm_num)
  letI instNNF : NontriviallyNormedField (𝔭.adicCompletion K) :=
    Valued.toNontriviallyNormedField (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ))

  haveI : (Valued.v : Valuation (𝔮.adicCompletion L)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne Valued.v (e := 2) (by norm_num)
  letI instNNF_L : NontriviallyNormedField (𝔮.adicCompletion L) :=
    Valued.toNontriviallyNormedField (𝔮.adicCompletion L) (WithZero (Multiplicative ℤ))

  haveI : ContinuousSMul (𝔭.adicCompletion K) (𝔮.adicCompletion L) := by
    apply continuousSMul_of_algebraMap
    show Continuous (AdicCompletionAlgebra.adicCompletionMap K 𝔭 𝔮 h𝔮_over_𝔭)
    exact UniformSpace.Completion.continuous_extension

  haveI := isScalarTower_adicCompletion (L := L) K 𝔭 𝔮 h𝔮_over_𝔭

  let Φ := (Algebra.TensorProduct.lift
      (Algebra.algHom (𝔭.adicCompletion K) (𝔭.adicCompletion K) (𝔮.adicCompletion L))
      (Algebra.algHom K L (𝔮.adicCompletion L))
      (fun x y => mul_comm _ _)).toLinearMap
  have h_dense : DenseRange Φ := by
    apply Dense.mono _ (𝔮.denseRange_algebraMap L)
    intro a ⟨l, hl⟩
    exact ⟨1 ⊗ₜ[K] l, by simp [Φ, Algebra.algHom, hl]⟩
  have h_closed : IsClosed (Φ.range : Set (𝔮.adicCompletion L)) :=
    Submodule.closed_of_finiteDimensional Φ.range
  have h_surj : Function.Surjective Φ := by
    rw [← Set.range_eq_univ, ← LinearMap.coe_range,
      ← h_closed.closure_eq]
    exact h_dense.closure_range

  haveI hfd : FiniteDimensional (𝔭.adicCompletion K) (𝔮.adicCompletion L) :=
    Module.Finite.of_surjective Φ h_surj


  have hadjoin_top : Algebra.adjoin (𝔭.adicCompletion K)
      (Set.range (algebraMap L (𝔮.adicCompletion L))) = ⊤ := by

    let Φ_alg := Algebra.TensorProduct.lift
        (Algebra.algHom (𝔭.adicCompletion K) (𝔭.adicCompletion K) (𝔮.adicCompletion L))
        (Algebra.algHom K L (𝔮.adicCompletion L))
        (fun _ _ => mul_comm _ _)
    have h_surj_alg : Function.Surjective Φ_alg := h_surj
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := h_surj_alg x
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp only [map_zero]; exact Subalgebra.zero_mem _
    · intro k l
      show Φ_alg (k ⊗ₜ[K] l) ∈ Algebra.adjoin (𝔭.adicCompletion K)
          (Set.range (algebraMap L (𝔮.adicCompletion L)))
      simp only [Φ_alg, Algebra.TensorProduct.lift_tmul]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ k)
        (Algebra.subset_adjoin ⟨l, rfl⟩)
    · exact fun a b ha hb => (map_add Φ_alg a b) ▸ Subalgebra.add_mem _ ha hb


  classical
  obtain ⟨p, hsep, hsplit⟩ := (IsGalois.tfae.out 0 3).mp hgal
  set_option maxHeartbeats 800000 in
  haveI : Polynomial.IsSplittingField (𝔭.adicCompletion K) (𝔮.adicCompletion L)
      (Polynomial.map (algebraMap K (𝔭.adicCompletion K)) p) := {
    splits' := by
      rw [Polynomial.map_map]
      have h1 := hsplit.splits'.map (algebraMap L (𝔮.adicCompletion L))
      rwa [Polynomial.map_map, show (algebraMap L (𝔮.adicCompletion L)).comp (algebraMap K L) =
        (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)).comp
          (algebraMap K (𝔭.adicCompletion K)) from by
        rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]] at h1

    adjoin_rootSet' := by
      rw [eq_top_iff, ← hadjoin_top]
      apply Algebra.adjoin_le
      intro x ⟨l, hl⟩; subst hl
      have hmem : l ∈ Algebra.adjoin K (p.rootSet L) :=
        hsplit.adjoin_rootSet' ▸ Algebra.mem_top
      have h1 : (algebraMap L (𝔮.adicCompletion L)) l ∈
          Subalgebra.map (IsScalarTower.toAlgHom K L (𝔮.adicCompletion L))
            (Algebra.adjoin K (p.rootSet L)) := ⟨l, hmem, rfl⟩
      rw [AlgHom.map_adjoin] at h1
      have h2 : Algebra.adjoin K
          ((IsScalarTower.toAlgHom K L (𝔮.adicCompletion L)) '' (p.rootSet L)) ≤
          (Algebra.adjoin (𝔭.adicCompletion K)
            ((IsScalarTower.toAlgHom K L (𝔮.adicCompletion L)) '' (p.rootSet L))).restrictScalars K := by
        apply Algebra.adjoin_le
        intro x hx; show x ∈ Algebra.adjoin (𝔭.adicCompletion K) _
        exact Algebra.subset_adjoin hx
      have h3 := h2 h1
      have himg : (IsScalarTower.toAlgHom K L (𝔮.adicCompletion L)) '' (p.rootSet L) ⊆
          (Polynomial.map (algebraMap K (𝔭.adicCompletion K)) p).rootSet (𝔮.adicCompletion L) := by
        intro y ⟨r, hr, hry⟩; subst hry
        simp only [Polynomial.rootSet, Finset.mem_coe, Multiset.mem_toFinset] at hr ⊢
        rw [Polynomial.mem_aroots] at hr ⊢
        refine ⟨Polynomial.map_ne_zero_iff (algebraMap K (𝔭.adicCompletion K)).injective |>.mpr hr.1, ?_⟩
        simp only [IsScalarTower.toAlgHom_apply, Polynomial.aeval_map_algebraMap,
                   Polynomial.aeval_algebraMap_apply (𝔮.adicCompletion L) r p, hr.2, map_zero]
      exact Algebra.adjoin_mono himg h3
  }
  exact @IsGalois.of_separable_splitting_field (𝔭.adicCompletion K) _ (𝔮.adicCompletion L) _ _
    (Polynomial.map (algebraMap K (𝔭.adicCompletion K)) p) this (hsep.map)

universe u_A u_K u_L u_B in
open IsDedekindDomain in
theorem adjoin_range_algebraMap_adicCompletion_eq_top
    (A : Type u_A) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u_L) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type u_B) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [IsFractionRing B L]
    [𝔮.asIdeal.LiesOver 𝔭.asIdeal] :
    letI := instAlgebraAdicCompletionOfLiesOver (L := L) K 𝔭 𝔮 h𝔮_over_𝔭
    Algebra.adjoin (𝔭.adicCompletion K)
      (Set.range (algebraMap L (𝔮.adicCompletion L))) = ⊤ := by
  letI := instAlgebraAdicCompletionOfLiesOver (L := L) K 𝔭 𝔮 h𝔮_over_𝔭

  haveI : (Valued.v : Valuation (𝔭.adicCompletion K)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne Valued.v (e := 2) (by norm_num)
  letI instNNF : NontriviallyNormedField (𝔭.adicCompletion K) :=
    Valued.toNontriviallyNormedField (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ))

  haveI : (Valued.v : Valuation (𝔮.adicCompletion L)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne Valued.v (e := 2) (by norm_num)
  letI instNNF_L : NontriviallyNormedField (𝔮.adicCompletion L) :=
    Valued.toNontriviallyNormedField (𝔮.adicCompletion L) (WithZero (Multiplicative ℤ))

  haveI : ContinuousSMul (𝔭.adicCompletion K) (𝔮.adicCompletion L) := by
    apply continuousSMul_of_algebraMap
    show Continuous (AdicCompletionAlgebra.adicCompletionMap K 𝔭 𝔮 h𝔮_over_𝔭)
    exact UniformSpace.Completion.continuous_extension

  haveI := isScalarTower_adicCompletion (L := L) K 𝔭 𝔮 h𝔮_over_𝔭

  haveI hfd : FiniteDimensional (𝔭.adicCompletion K) (𝔮.adicCompletion L) := by
    let Φ := (Algebra.TensorProduct.lift
        (Algebra.algHom (𝔭.adicCompletion K) (𝔭.adicCompletion K) (𝔮.adicCompletion L))
        (Algebra.algHom K L (𝔮.adicCompletion L))
        (fun x y => mul_comm _ _)).toLinearMap
    have h_dense : DenseRange Φ := by
      apply Dense.mono _ (𝔮.denseRange_algebraMap L)
      intro a ⟨l, hl⟩
      exact ⟨1 ⊗ₜ[K] l, by simp [Φ, Algebra.algHom, hl]⟩
    have h_closed : IsClosed (Φ.range : Set (𝔮.adicCompletion L)) :=
      Submodule.closed_of_finiteDimensional Φ.range
    have h_surj : Function.Surjective Φ := by
      rw [← Set.range_eq_univ, ← LinearMap.coe_range,
        ← h_closed.closure_eq]
      exact h_dense.closure_range
    exact Module.Finite.of_surjective Φ h_surj

  set S := Algebra.adjoin (𝔭.adicCompletion K)
    (Set.range (algebraMap L (𝔮.adicCompletion L))) with hS_def

  haveI : FiniteDimensional (𝔭.adicCompletion K) S.toSubmodule :=
    Submodule.finiteDimensional_of_le le_top

  have hS_closed : IsClosed (S.toSubmodule : Set (𝔮.adicCompletion L)) :=
    Submodule.closed_of_finiteDimensional S.toSubmodule

  have hS_carrier : (S : Set (𝔮.adicCompletion L)) = (S.toSubmodule : Set (𝔮.adicCompletion L)) :=
    rfl

  have hS_closed' : IsClosed (S : Set (𝔮.adicCompletion L)) :=
    hS_carrier ▸ hS_closed

  have h_range_sub : Set.range (algebraMap L (𝔮.adicCompletion L)) ⊆ ↑S :=
    Algebra.subset_adjoin

  have h_dense : Dense (Set.range (algebraMap L (𝔮.adicCompletion L))) :=
    𝔮.denseRange_algebraMap L

  have hS_dense : Dense (S : Set (𝔮.adicCompletion L)) :=
    h_dense.mono h_range_sub

  have hS_eq_univ : (S : Set (𝔮.adicCompletion L)) = Set.univ := by
    rw [← hS_closed'.closure_eq, hS_dense.closure_eq]
  rw [SetLike.ext'_iff]
  simp [hS_eq_univ]

universe u_A u_K u_L u_B in
open IsDedekindDomain in
theorem thm_11_23_part6_galois_implication
    (A : Type u_A) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u_L) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type u_B) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [IsFractionRing B L]
    [𝔮.asIdeal.LiesOver 𝔭.asIdeal]
    (hgal : IsGalois K L) :
    letI := instAlgebraAdicCompletionOfLiesOver (L := L) K 𝔭 𝔮 h𝔮_over_𝔭
    IsGalois (𝔭.adicCompletion K) (𝔮.adicCompletion L) ∧
    ∃ (φ : (𝔮.adicCompletion L ≃ₐ[𝔭.adicCompletion K] 𝔮.adicCompletion L) →*
          (L ≃ₐ[K] L)),
      Function.Injective φ := by
  letI inst_alg := instAlgebraAdicCompletionOfLiesOver (L := L) K 𝔭 𝔮 h𝔮_over_𝔭


  have hIsGalois : IsGalois (𝔭.adicCompletion K) (𝔮.adicCompletion L) := by


    exact isGalois_adicCompletion A K L B 𝔭 𝔮 h𝔮_over_𝔭 hgal


  have hInj : ∃ (φ : (𝔮.adicCompletion L ≃ₐ[𝔭.adicCompletion K]
        𝔮.adicCompletion L) →* (L ≃ₐ[K] L)),
      Function.Injective φ := by

    haveI h_sc : IsScalarTower K (𝔭.adicCompletion K) (𝔮.adicCompletion L) :=
      isScalarTower_adicCompletion K 𝔭 𝔮 h𝔮_over_𝔭
    haveI h_sc2 : IsScalarTower K L (𝔮.adicCompletion L) := inferInstance
    have h_gen : Algebra.adjoin (𝔭.adicCompletion K)
        (Set.range (algebraMap L (𝔮.adicCompletion L))) = ⊤ := by
      exact adjoin_range_algebraMap_adicCompletion_eq_top A K L B 𝔭 𝔮 h𝔮_over_𝔭
    haveI : Normal K L := IsGalois.to_normal

    refine ⟨(AlgEquiv.restrictNormalHom (F := K) (K₁ := 𝔮.adicCompletion L) L).comp
      ⟨⟨fun σ => AlgEquiv.restrictScalars K σ, rfl⟩, fun _ _ => rfl⟩, ?_⟩

    intro σ τ hστ
    simp only [MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk] at hστ

    have h_eq : ∀ y : L, σ (algebraMap L (𝔮.adicCompletion L) y) =
        τ (algebraMap L (𝔮.adicCompletion L) y) := by
      intro y
      have h1 := AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) L y
      have h2 := AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) L y
      rw [AlgEquiv.restrictScalars_apply] at h1 h2
      rw [← h1, ← h2]
      congr 1
      exact AlgEquiv.ext_iff.mp hστ y

    ext x
    have h_alg : ∀ y ∈ Set.range (algebraMap L (𝔮.adicCompletion L)),
        (σ.toAlgHom : 𝔮.adicCompletion L →ₐ[𝔭.adicCompletion K] 𝔮.adicCompletion L) y =
        (τ.toAlgHom : 𝔮.adicCompletion L →ₐ[𝔭.adicCompletion K] 𝔮.adicCompletion L) y := by
      rintro _ ⟨y, rfl⟩
      simp only [AlgEquiv.toAlgHom_eq_coe]
      exact h_eq y
    exact AlgHom.ext_iff.mp (AlgHom.ext_of_adjoin_eq_top h_gen h_alg) x
  exact ⟨hIsGalois, hInj⟩

universe u_A u_K u_L u_B in
open IsDedekindDomain in
theorem theorem_11_23_part1_separable
    (A : Type*) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type*) [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    [IsScalarTower K (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    [IsScalarTower K L (𝔮.adicCompletion L)]
    [FiniteDimensional (𝔭.adicCompletion K) (𝔮.adicCompletion L)] :
    Algebra.IsSeparable (𝔭.adicCompletion K) (𝔮.adicCompletion L) := by


  haveI : CharZero (𝔭.adicCompletion K) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective K (𝔭.adicCompletion K))

  haveI : Algebra.IsAlgebraic (𝔭.adicCompletion K) (𝔮.adicCompletion L) :=
    Algebra.IsAlgebraic.of_finite (𝔭.adicCompletion K) (𝔮.adicCompletion L)


  exact ⟨fun x => (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)).separable⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
open IsDedekindDomain in
theorem theorem_11_23_part2_unique_prime
    (A : Type*) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
    IsDiscreteValuationRing (𝔮.adicCompletionIntegers L) := inferInstance

open IsDedekindDomain in
end KroneckerWeber

def no_Z4Z_cube_extension := @KroneckerWeber.lemma_20_11_no_Z4Z3

def lemma_20_11 := @KroneckerWeber.lemma_20_11
def theorem_11_23_part1_separable := @KroneckerWeber.theorem_11_23_part1_separable
def theorem_11_23_part2_unique_prime := @KroneckerWeber.theorem_11_23_part2_unique_prime
def thm_11_23_part6_galois_implication := @KroneckerWeber.thm_11_23_part6_galois_implication
end
