/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import sympy.atlas.v1.Atlas.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import sympy.atlas.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace NumberField.Adeles

inductive Place (K : Type*) [Field K] [NumberField K] where
  | finite : HeightOneSpectrum (𝓞 K) → Place K
  | infinite : InfinitePlace K → Place K

instance instDecidableEqPlace (K : Type*) [Field K] [NumberField K] :
    DecidableEq (Place K) :=
  Classical.decEq _

variable {K : Type*} [Field K] [NumberField K]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem adicCompletion_finite_residueField
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Empty.Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  haveI : Empty.Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Empty.Finite.of_equiv (𝓞 K ⧸ v.asIdeal)
    (KroneckerWeber.completion_residueFieldEquiv (𝓞 K) K v).symm.toEquiv

noncomputable instance adicCompletion_compactSpace_integer
    (v : HeightOneSpectrum (𝓞 K)) :
    CompactSpace (Valued.integer (v.adicCompletion K)) := by
  letI := Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  exact ⟨(Valued.isClosed_integer _).completeSpace_coe,
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)),
    adicCompletion_finite_residueField K v⟩

noncomputable instance adicCompletion_properSpace
    (v : HeightOneSpectrum (𝓞 K)) :
    ProperSpace (v.adicCompletion K) := by
  letI := Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  exact Valued.integer.properSpace_iff_compactSpace_integer.mpr
    (adicCompletion_compactSpace_integer v)

lemma isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (↑(v.adicCompletionIntegers K) : Set (v.adicCompletion K)) := by
  change IsCompact (Valued.integer (v.adicCompletion K) : Set (v.adicCompletion K))
  have := (adicCompletion_compactSpace_integer v).isCompact_univ
  rwa [Subtype.isCompact_iff, Set.image_univ, Subtype.range_val] at this

abbrev adeleRing := AdeleRing (𝓞 K) K

def placeNorm (v : Place K) (x : K) : ℝ :=
  match v with
  | .finite vi => NumberField.HeightOneSpectrum.adicAbv K vi x
  | .infinite w => w x

def placeNormAdele (v : Place K) (a : adeleRing (K := K)) : ℝ :=
  match v with
  | .finite vi => ‖a.2 vi‖
  | .infinite w => ‖a.1 w‖

def adelicAbsVal (a : adeleRing (K := K)) : ℝ :=
  (∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult) *
  (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖)

section RestrictedProductDirectLimit

open Filter Set Topology

instance adeleRing_isTopologicalRing : IsTopologicalRing (adeleRing (K := K)) :=
  inferInstance

instance infiniteAdeleRing_t2Space : T2Space (InfiniteAdeleRing K) := Pi.t2Space

instance finiteAdeleRing_t2Space : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite))

instance adeleRing_t2Space : T2Space (adeleRing (K := K)) :=
  Prod.t2Space

instance finiteAdeleRing_locallyCompactSpace :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := by


  letI wlcs : WeaklyLocallyCompactSpace (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite) :=
    RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite
      (fun v => by convert Valued.isOpen_integer (v.adicCompletion K) using 1)
      (Filter.Eventually.of_forall (fun v => isCompact_adicCompletionIntegers v))

  letI : WeaklyLocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := wlcs

  infer_instance

instance adeleRing_locallyCompactSpace : LocallyCompactSpace (adeleRing (K := K)) :=
  Prod.locallyCompactSpace _ _

abbrev principalSubgroup : AddSubgroup (adeleRing (K := K)) :=
  AdeleRing.principalSubgroup (𝓞 K) K

instance infinitePlace_properSpace (v : InfinitePlace K) :
    ProperSpace v.Completion := by
  open InfinitePlace.Completion in
  constructor
  intro x r
  rcases v.isReal_or_isComplex with hv | hv
  · have e := isometryEquivRealOfIsReal hv
    rw [show Metric.closedBall x r = e.symm '' (Metric.closedBall (e x) r) from ?_]
    · exact (isCompact_closedBall (e x) r).image e.symm.continuous
    · ext y; simp only [Set.mem_image, Metric.mem_closedBall]
      exact ⟨fun h => ⟨e y, by rwa [e.dist_eq], by simp⟩,
             fun ⟨z, hz, hzy⟩ => by rw [← hzy, ← e.dist_eq]; simpa using hz⟩
  · have e := isometryEquivComplexOfIsComplex hv
    rw [show Metric.closedBall x r = e.symm '' (Metric.closedBall (e x) r) from ?_]
    · exact (isCompact_closedBall (e x) r).image e.symm.continuous
    · ext y; simp only [Set.mem_image, Metric.mem_closedBall]
      exact ⟨fun h => ⟨e y, by rwa [e.dist_eq], by simp⟩,
             fun ⟨z, hz, hzy⟩ => by rw [← hzy, ← e.dist_eq]; simpa using hz⟩

open scoped Classical in
noncomputable def coveringBound (K : Type*) [Field K] [NumberField K] : ℝ :=
  max 1 (∑ i, ‖mixedEmbedding.latticeBasis K i‖)

def PiTensorCompletion (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L] :=
  (v : InfinitePlace K) → (L ⊗[K] v.Completion)

instance piTensorCompletion_commRing (K L : Type*)
    [Field K] [NumberField K] [Field L] [Algebra K L] :
    CommRing (PiTensorCompletion K L) := Pi.commRing

attribute [local instance] WithAbs.algebraLeft

set_option backward.isDefEq.respectTransparency false in
noncomputable def tensorCompletionToFiberProd
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) :
    L ⊗[K] v.Completion →+*
      ((w : { w : InfinitePlace L // w.comap (algebraMap K L) = v }) → w.val.Completion) := by
  apply Pi.ringHom
  intro ⟨w, hw⟩
  letI : Algebra K w.Completion := Algebra.restrictScalars K L w.Completion
  haveI : IsScalarTower K L w.Completion := by
    constructor; intro x y z; change (x • y) • z = x • (y • z); simp [smul_assoc]
  haveI : w.1.LiesOver v.1 := ⟨by
    have h1 : (w.comap (algebraMap K L)).1 = v.1 := by rw [hw]
    rw [← h1]; rfl⟩
  haveI itv : IsTopologicalRing (WithAbs v.1) := inferInstance
  haveI itw : IsTopologicalRing (WithAbs w.1) := inferInstance
  haveI uv : IsUniformAddGroup (WithAbs v.1) := inferInstance
  haveI uw : IsUniformAddGroup (WithAbs w.1) := inferInstance
  have hiso := InfinitePlace.LiesOver.isometry_algebraMap w (v := v)
  let isoHom : v.Completion →+* w.Completion :=
    @Isometry.mapRingHom _ _ _ _ itv uv _ _ uw itw
      (algebraMap (WithAbs v.1) (WithAbs w.1)) hiso
  let vToW : v.Completion →ₐ[K] w.Completion := {
    toRingHom := isoHom
    commutes' := by
      intro r
      change @Isometry.mapRingHom _ _ _ _ itv uv _ _ uw itw
        (algebraMap (WithAbs v.1) (WithAbs w.1)) hiso
        (↑(algebraMap K (WithAbs v.1) r)) = algebraMap K w.Completion r
      rw [@Isometry.mapRingHom_coe _ _ _ _ itv uv _ _ uw itw _ hiso]
      congr 1
  }
  let lToW : L →ₐ[K] w.Completion := {
    toRingHom := algebraMap L w.Completion
    commutes' := fun _ => rfl
  }
  exact (Algebra.TensorProduct.productMap lToW vToW).toRingHom


def sigmaPiRegroup (K L : Type*) [Field K] [Field L] [Algebra K L] :
    ((v : InfinitePlace K) →
      (w : { w : InfinitePlace L // w.comap (algebraMap K L) = v }) → w.val.Completion) ≃+*
    InfiniteAdeleRing L :=
  RingEquiv.mk
    { toFun := fun g w => g (w.comap (algebraMap K L)) ⟨w, rfl⟩
      invFun := fun h _v ⟨w, _⟩ => h w
      left_inv := fun g => by ext v ⟨w, hw⟩; subst hw; rfl
      right_inv := fun _ => rfl }
    (fun _ _ => rfl) (fun _ _ => rfl)

instance finAdeleRing_algebra_base (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    Algebra K (FiniteAdeleRing (𝓞 L) L) :=
  ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap K L)).toAlgebra

instance finAdeleRing_scalarTower_base_base (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    IsScalarTower K K (FiniteAdeleRing (𝓞 L) L) :=
  ⟨fun r s x => by simp [Algebra.smul_def, mul_assoc]⟩

instance finAdeleRing_scalarTower_base_ext (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    IsScalarTower K L (FiniteAdeleRing (𝓞 L) L) := by
  constructor; intro r l x; simp only [Algebra.smul_def]; rw [map_mul, mul_assoc]; rfl

noncomputable def primeBelow (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))
  isPrime := Ideal.IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))
  ne_bot := by intro h; exact w.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)

noncomputable def localBaseChangeMap (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    WithVal (HeightOneSpectrum.valuation K (primeBelow K L w)) →+*
      w.adicCompletion L :=
  (UniformSpace.Completion.coeRingHom (α := WithVal (HeightOneSpectrum.valuation L w))).comp
    ((WithVal.equiv (HeightOneSpectrum.valuation L w)).symm.toRingHom.comp
      ((algebraMap K L).comp
        (WithVal.equiv (HeightOneSpectrum.valuation K (primeBelow K L w))).toRingHom))

lemma localBaseChangeMap_continuous (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    Continuous (localBaseChangeMap K L w) := by
  set v := primeBelow K L w
  set g : WithVal (HeightOneSpectrum.valuation K v) →+*
      WithVal (HeightOneSpectrum.valuation L w) :=
    (WithVal.equiv (HeightOneSpectrum.valuation L w)).symm.toRingHom.comp
      ((algebraMap K L).comp
        (WithVal.equiv (HeightOneSpectrum.valuation K v)).toRingHom) with hg_def

  show Continuous (UniformSpace.Completion.coeRingHom.comp g)
  apply Continuous.comp (UniformSpace.Completion.continuous_coe _)


  exact algebraMap_withVal_continuous_general K v w (le_refl _)

noncomputable def baseChangeAtPrime (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    (primeBelow K L w).adicCompletion K →+* w.adicCompletion L :=
  UniformSpace.Completion.extensionHom
    (localBaseChangeMap K L w) (localBaseChangeMap_continuous K L w)

lemma baseChangeAtPrime_mem_integers (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L))
    (x : (primeBelow K L w).adicCompletion K)
    (hx : x ∈ (primeBelow K L w).adicCompletionIntegers K) :
    (baseChangeAtPrime K L w) x ∈ w.adicCompletionIntegers L := by

  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx


  have hclosed : IsClosed {y : (primeBelow K L w).adicCompletion K |
      Valued.v y ≤ 1 → Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} := by
    have h1 : {y : (primeBelow K L w).adicCompletion K |
        Valued.v y ≤ 1 → Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} =
        {y | ¬(Valued.v y ≤ 1)} ∪ {y | Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} := by
      ext y; simp only [Set.mem_setOf_eq, Set.mem_union]; tauto
    rw [h1]
    apply IsClosed.union
    ·
      have : {y : (primeBelow K L w).adicCompletion K | ¬(Valued.v y ≤ 1)} =
          ((Valued.v.valuationSubring :
            ValuationSubring ((primeBelow K L w).adicCompletion K)) :
            Set ((primeBelow K L w).adicCompletion K))ᶜ := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, SetLike.mem_coe,
          Valuation.mem_valuationSubring_iff]
      rw [this]
      exact (Valued.isClopen_valuationSubring
        ((primeBelow K L w).adicCompletion K)).2.isClosed_compl
    ·
      have hf_cont : Continuous (baseChangeAtPrime K L w) :=
        UniformSpace.Completion.continuous_extension
      have : {y : (primeBelow K L w).adicCompletion K |
          Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} =
          (baseChangeAtPrime K L w :
            (primeBelow K L w).adicCompletion K → w.adicCompletion L) ⁻¹'
            ((Valued.v.valuationSubring : ValuationSubring (w.adicCompletion L)) :
              Set (w.adicCompletion L)) := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
          Valuation.mem_valuationSubring_iff]
      rw [this]
      exact (Valued.isClosed_valuationSubring (w.adicCompletion L)).preimage hf_cont

  have hdense : ∀ (k : WithVal (HeightOneSpectrum.valuation K (primeBelow K L w))),
      Valued.v (↑k : (primeBelow K L w).adicCompletion K) ≤ 1 →
        Valued.v ((baseChangeAtPrime K L w) (↑k : (primeBelow K L w).adicCompletion K)) ≤ 1 := by
    intro k hk
    rw [Valued.valuedCompletion_apply] at hk

    have hf_coe : (baseChangeAtPrime K L w) (↑k : (primeBelow K L w).adicCompletion K) =
        localBaseChangeMap K L w k :=
      UniformSpace.Completion.extensionHom_coe _ (localBaseChangeMap_continuous K L w) k
    rw [hf_coe]


    have hval : Valued.v ((localBaseChangeMap K L w) k) =
        HeightOneSpectrum.valuation L w (algebraMap K L
          ((WithVal.equiv (HeightOneSpectrum.valuation K (primeBelow K L w))) k)) := by
      simp only [localBaseChangeMap, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      erw [Valued.valuedCompletion_apply]
      rw [← WithVal.val_apply_equiv (HeightOneSpectrum.valuation L w)]
      simp only [RingEquiv.apply_symm_apply]
    rw [hval]


    haveI : w.asIdeal.LiesOver (primeBelow K L w).asIdeal := ⟨rfl⟩
    rw [valuation_extends_with_ramificationIdx K L (primeBelow K L w) w]
    rw [WithVal.val_apply_equiv]
    exact pow_le_one₀ (WithZero.zero_le _) hk


  exact UniformSpace.Completion.induction_on x hclosed (fun k => hdense k) hx

lemma baseChange_restricted_condition (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (a : FiniteAdeleRing (𝓞 K) K) :
    ∀ᶠ (w : HeightOneSpectrum (𝓞 L)) in Filter.cofinite,
      (baseChangeAtPrime K L w) (a (primeBelow K L w)) ∈
        ↑(w.adicCompletionIntegers L) := by


  have ha := a.property

  rw [Filter.eventually_cofinite] at ha ⊢


  set S := {v : HeightOneSpectrum (𝓞 K) | a v ∉ (v.adicCompletionIntegers K : Set (v.adicCompletion K))} with hS_def

  apply Set.Finite.subset (s := primeBelow K L ⁻¹' S)
  ·


    have hS_eq : primeBelow K L ⁻¹' S = ⋃ v ∈ S, {w | primeBelow K L w = v} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨primeBelow K L w, h, rfl⟩, fun ⟨v, hv, hvw⟩ => hvw ▸ hv⟩
    rw [hS_eq]
    apply ha.biUnion
    intro v _


    have hinj : Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 L)) :=
      fun a b h => HeightOneSpectrum.ext_iff.mpr h
    apply Set.Finite.subset ((primesOver_finite v.asIdeal (𝓞 L)).preimage hinj.injOn)
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hw ⊢
    refine ⟨w.isPrime, ⟨?_⟩⟩
    show v.asIdeal = Ideal.under (𝓞 K) w.asIdeal
    rw [Ideal.under, ← hw]
    rfl

  ·
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS_def] at hw ⊢


    intro hmem
    exact hw (baseChangeAtPrime_mem_integers K L w _ hmem)

lemma baseChange_commutes (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (k : K) :
    (RestrictedProduct.mk
      (fun w => (baseChangeAtPrime K L w)
        ((algebraMap K (FiniteAdeleRing (𝓞 K) K) k) (primeBelow K L w)))
      (baseChange_restricted_condition K L (algebraMap K (FiniteAdeleRing (𝓞 K) K) k))) =
    algebraMap K (FiniteAdeleRing (𝓞 L) L) k := by
  apply RestrictedProduct.ext; intro w
  simp only [RestrictedProduct.mk_apply]

  have hLHS : ((algebraMap K (FiniteAdeleRing (𝓞 K) K)) k) (primeBelow K L w) =
    (algebraMap K ((primeBelow K L w).adicCompletion K) k) := rfl
  rw [hLHS]

  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp]

  simp only [baseChangeAtPrime, UniformSpace.Completion.extensionHom_coe]

  simp only [localBaseChangeMap, RingHom.comp_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rfl

noncomputable def finAdeleRing_baseChangeHom (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    FiniteAdeleRing (𝓞 K) K →ₐ[K] FiniteAdeleRing (𝓞 L) L where
  toFun a := RestrictedProduct.mk
    (fun w => (baseChangeAtPrime K L w) (a (primeBelow K L w)))
    (baseChange_restricted_condition K L a)
  map_one' := by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (1 : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) = 1 from rfl, map_one]
    rfl
  map_mul' := fun a b => by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (a * b : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) =
      a (primeBelow K L w) * b (primeBelow K L w) from rfl, map_mul]
    rfl
  map_zero' := by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (0 : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) = 0 from rfl, map_zero]
    rfl
  map_add' := fun a b => by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (a + b : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) =
      a (primeBelow K L w) + b (primeBelow K L w) from rfl, map_add]
    rfl
  commutes' := fun k => baseChange_commutes K L k

def finAdeleRing_includeExt (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    L →ₐ[K] FiniteAdeleRing (𝓞 L) L :=
  (Algebra.ofId L (FiniteAdeleRing (𝓞 L) L)).restrictScalars K

def finAdeleRing_tensor_forward (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    (FiniteAdeleRing (𝓞 K) K ⊗[K] L) →ₐ[K] FiniteAdeleRing (𝓞 L) L :=
  Algebra.TensorProduct.lift (finAdeleRing_baseChangeHom K L)
    (finAdeleRing_includeExt K L) (fun _ _ => Commute.all _ _)

instance adeleRing_algebra_base (L : Type*) [Field L] [NumberField L]
    [Algebra K L] :
    Algebra K (AdeleRing (𝓞 L) L) :=
  Algebra.compHom (AdeleRing (𝓞 L) L) (algebraMap K L)

def adelicBox (a : adeleRing (K := K)) : Set (adeleRing (K := K)) :=
  { t | (∀ v : HeightOneSpectrum (𝓞 K), ‖t.2 v‖ ≤ ‖a.2 v‖) ∧
        (∀ w : InfinitePlace K, ‖t.1 w‖ ≤ ‖a.1 w‖ / 4) }

instance instNormOneClass_Completion (w : InfinitePlace K) : NormOneClass w.Completion where
  norm_one := by
    have : (1 : w.Completion) = algebraMap K w.Completion 1 := (map_one _).symm
    rw [this, show algebraMap K w.Completion 1 =
      (↑((WithAbs.equiv w.1).symm 1) : w.Completion) from rfl]
    rw [InfinitePlace.Completion.norm_coe]; simp

instance instNontrivNormedField_InfCompl (w : InfinitePlace K) :
    NontriviallyNormedField w.Completion := by
  refine { InfinitePlace.Completion.instNormedField w with non_trivial := ?_ }
  use algebraMap K w.Completion 2
  rw [show algebraMap K w.Completion 2 =
    (↑((WithAbs.equiv w.1).symm 2) : w.Completion) from rfl]
  rw [InfinitePlace.Completion.norm_coe]
  show 1 < w 2
  rw [(w.norm_embedding_eq 2).symm]; simp only [map_ofNat]; norm_num

def placeCompletion : Place K → Type _
  | .finite vi => vi.adicCompletion K
  | .infinite w => w.Completion

instance instTopologicalSpacePlaceCompletion (v : Place K) :
    TopologicalSpace (placeCompletion v) := by
  cases v with
  | finite vi => exact inferInstance
  | infinite w => exact inferInstance

def placeIntegerSet : (v : Place K) → Set (placeCompletion v)
  | .finite vi => (vi.adicCompletionIntegers K : Set (vi.adicCompletion K))
  | .infinite _ => Set.univ

abbrev restrictedProductAwayFrom (w : Place K) : Type _ :=
  RestrictedProduct
    (fun (v : {v : Place K // v ≠ w}) => placeCompletion v.val)
    (fun (v : {v : Place K // v ≠ w}) => placeIntegerSet v.val)
    Filter.cofinite

@[reducible]
def embedAtPlace : (v : Place K) → K → placeCompletion v
  | .finite vi => algebraMap K (vi.adicCompletion K)
  | .infinite w => algebraMap K w.Completion

def diagonalAwayFrom (w : Place K) (x : K) : restrictedProductAwayFrom w :=
  RestrictedProduct.mk
    (fun (v : {v : Place K // v ≠ w}) => embedAtPlace v.val x)
    (by


     rw [Filter.eventually_cofinite]

     set f : {v : Place K // v ≠ w} → Option (HeightOneSpectrum (𝓞 K)) :=
       fun i => match i.val with
         | .finite vi => some vi
         | .infinite _ => none
     apply Set.Finite.of_injOn (f := f)
       (t := Option.some '' HeightOneSpectrum.Support (𝓞 K) x)
     ·
       intro ⟨v, hv⟩ hmem
       simp only [Set.mem_setOf_eq] at hmem
       cases v with
       | infinite _ => simp [placeIntegerSet] at hmem
       | finite vi =>
         simp only [f, Set.mem_image]
         refine ⟨vi, ?_, rfl⟩
         rw [HeightOneSpectrum.Support, Set.mem_setOf_eq]
         simp only [placeIntegerSet, SetLike.mem_coe, embedAtPlace] at hmem
         rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hmem
         have : algebraMap K (vi.adicCompletion K) x = (x : vi.adicCompletion K) := rfl
         rw [this] at hmem
         rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hmem
     ·
       intro ⟨v₁, hv₁⟩ hmem₁ ⟨v₂, hv₂⟩ hmem₂ hfeq
       simp only [Set.mem_setOf_eq] at hmem₁ hmem₂
       cases v₁ with
       | infinite _ => simp [placeIntegerSet] at hmem₁
       | finite vi₁ =>
         cases v₂ with
         | infinite _ => simp [placeIntegerSet] at hmem₂
         | finite vi₂ =>
           simp only [f] at hfeq
           have : vi₁ = vi₂ := Option.some_injective _ hfeq
           subst this; rfl
     ·
       exact (HeightOneSpectrum.Support.finite (𝓞 K) x).image _)
