/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import sympy.atlas.v1.Atlas.NumberTheoryI.code.CompleteFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import sympy.atlas.v1.Atlas.NumberTheoryI.code.KroneckerWeber

noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

namespace AbsoluteValue

variable {K : Type*} [Field K]

def IsTrivial (v : AbsoluteValue K ℝ) : Prop :=
  ∀ x : K, x ≠ 0 → v x = 1

instance nontrivialAbsValSetoid :
    Setoid { v : AbsoluteValue K ℝ // ¬v.IsTrivial } where
  r v w := v.val.IsEquiv w.val
  iseqv := {
    refl := fun _ => AbsoluteValue.IsEquiv.refl _
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

def Place := Quotient (nontrivialAbsValSetoid K)

end Place

section PlaceExtension

def restrictPlace {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : NumberField.InfinitePlace L) : NumberField.InfinitePlace K :=
  w.comap (algebraMap K L)

def InfinitePlace.LiesAbove {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K) : Prop :=
  restrictPlace w = v

def FinitePlace.LiesAbove {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal

end PlaceExtension

instance instAlgebraBaseOfExtCompletion {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L] (w : NumberField.InfinitePlace L) :
    Algebra K w.Completion :=
  ((algebraMap L w.Completion).comp (algebraMap K L)).toAlgebra

instance instAlgebraBaseOfExtAdicCompletion {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    Algebra K (w.adicCompletion L) := inferInstance

section TensorProductDecomposition

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 80000

def algebraMapLToCompletion {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L] (w : NumberField.InfinitePlace L) :
    L →ₐ[K] w.Completion where
  toFun := algebraMap L w.Completion
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun _ => rfl

set_option backward.isDefEq.respectTransparency false in
def completionEmbedding {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K)
    (w : NumberField.InfinitePlace L) (hw : w.comap (algebraMap K L) = v) :
    v.Completion →ₐ[K] w.Completion := by
  haveI : w.1.LiesOver v.1 := ⟨by
    have : (w.comap (algebraMap K L)).1 = v.1 := by rw [hw]
    rw [← this]; rfl⟩
  let iso := LiesOver.isometry_algebraMap w (v := v)
  let f : v.Completion →+* w.Completion := iso.mapRingHom
  exact {
    toRingHom := f
    commutes' := by
      intro r
      show f (algebraMap K v.Completion r) = algebraMap K w.Completion r
      change f (↑(algebraMap K (WithAbs v.1) r)) = ↑(algebraMap K (WithAbs w.1) r)
      rw [iso.mapRingHom_coe]
      congr 1
  }

def canonicalMap {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    TensorProduct K L v.Completion →ₐ[K]
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) :=
  Pi.algHom K
    (fun (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) =>
      w.val.Completion)
    (fun (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) =>
      Algebra.TensorProduct.productMap
        (algebraMapLToCompletion w.val)
        (completionEmbedding v w.val w.prop))

instance nontriviallyNormedField_infinitePlace_completion {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) : NontriviallyNormedField v.Completion := by
  constructor; use 2
  have h1 : Completion.extensionEmbedding v 2 = (2 : ℂ) := by simp [map_ofNat]
  have h2 : ‖(2 : v.Completion)‖ = ‖(2 : ℂ)‖ := by
    rw [← h1]
    exact ((Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) 2).symm
  rw [h2]; norm_num

set_option backward.isDefEq.respectTransparency false in

def completionEmbedding_finite_ringHom {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) :
    WithVal (v.valuation K) →+* w.adicCompletion L :=
  (algebraMap K (w.adicCompletion L)).comp (WithVal.equiv (v.valuation K)).toRingHom


lemma multiplicative_toAdd_pow (h : Multiplicative ℤ) (e : ℕ) :
    Multiplicative.toAdd (h ^ e) = e * Multiplicative.toAdd h := by
  induction e with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, add_mul, one_mul]


lemma exists_pow_lt_of_ne_zero (m : WithZero (Multiplicative ℤ)) (hm : m ≠ 0)
    (e : ℕ) (he : e ≠ 0) :
    ∃ d : WithZero (Multiplicative ℤ), d ≠ 0 ∧ ∀ a : WithZero (Multiplicative ℤ),
      a < d → a ^ e < m := by
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.mp hm
  set n := Multiplicative.toAdd g
  use ↑(Multiplicative.ofAdd (n / (e : ℤ)))
  refine ⟨WithZero.coe_ne_zero, fun a ha => ?_⟩
  cases a with
  | zero => rw [zero_pow he]; exact WithZero.zero_lt_coe g
  | coe h =>
    rw [WithZero.coe_lt_coe] at ha
    rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
    suffices (e : ℤ) * Multiplicative.toAdd h < n by
      rwa [show h ^ e < g ↔ Multiplicative.toAdd (h ^ e) < n from Iff.rfl,
           multiplicative_toAdd_pow]
    have he_pos : (0 : ℤ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
    have hle : Multiplicative.toAdd h ≤ n / (e : ℤ) - 1 :=
      Int.le_sub_one_of_lt ha
    calc (e : ℤ) * Multiplicative.toAdd h
        ≤ (e : ℤ) * (n / (e : ℤ) - 1) := mul_le_mul_of_nonneg_left hle he_pos.le
      _ = (e : ℤ) * (n / (e : ℤ)) - (e : ℤ) := by ring
      _ ≤ n - 1 := by linarith [Int.ediv_mul_le n he_pos.ne']
      _ < n := by omega

set_option maxHeartbeats 1600000 in
theorem algebraMap_withVal_continuous {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hw : FinitePlace.LiesAbove w v) :
    Continuous
      ((WithVal.equiv (w.valuation L)).symm.toRingHom.comp
        ((algebraMap K L).comp (WithVal.equiv (v.valuation K)).toRingHom) :
        WithVal (v.valuation K) →+* WithVal (w.valuation L)) := by

  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩

  have hval : ∀ x : K, w.valuation L (algebraMap K L x) =
      (v.valuation K x) ^ (Ideal.ramificationIdx v.asIdeal w.asIdeal) :=
    fun x => valuation_extends_with_ramificationIdx K L v w x
  let e := Ideal.ramificationIdx v.asIdeal w.asIdeal
  have he : e ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot

  let f : WithVal (v.valuation K) →+* WithVal (w.valuation L) :=
    (WithVal.equiv (w.valuation L)).symm.toRingHom.comp
      ((algebraMap K L).comp (WithVal.equiv (v.valuation K)).toRingHom)
  show Continuous f

  have hfv : ∀ x : WithVal (v.valuation K),
      @Valued.v (WithVal (w.valuation L)) _ _ _ _ (f x) =
      (@Valued.v (WithVal (v.valuation K)) _ _ _ _ x) ^ e := by
    intro x
    rw [← WithVal.val_apply_equiv (w.valuation L)]
    show w.valuation L ((WithVal.equiv (w.valuation L)) ((WithVal.equiv (w.valuation L)).symm
      (algebraMap K L ((WithVal.equiv (v.valuation K)) x)))) = _
    rw [RingEquiv.apply_symm_apply, hval, ← WithVal.val_apply_equiv (v.valuation K)]

  apply continuous_of_continuousAt_zero f.toAddMonoidHom
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]

  intro γ


  set M := MonoidWithZeroHom.ValueGroup₀.embedding (↑γ : MonoidWithZeroHom.ValueGroup₀
    (@Valued.v (WithVal (w.valuation L)) _ _ _ _)) with hM_def
  have hM_ne : M ≠ 0 := by
    simp only [M, ne_eq, map_eq_zero]
    exact Units.ne_zero γ

  obtain ⟨d, hd_ne, hd_pow⟩ := exists_pow_lt_of_ne_zero M hM_ne e he


  obtain ⟨y, hy⟩ := v.valuation_surjective K d

  set y' : WithVal (v.valuation K) := (WithVal.equiv (v.valuation K)).symm y with hy'_def

  set δ_vg := MonoidWithZeroHom.ValueGroup₀.restrict₀
    (@Valued.v (WithVal (v.valuation K)) _ _ _ _) y' with hδ_vg_def

  have hδ_emb : MonoidWithZeroHom.ValueGroup₀.embedding δ_vg = d := by
    rw [hδ_vg_def, MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
    show @Valued.v (WithVal (v.valuation K)) _ _ _ _ y' = d
    rw [← WithVal.val_apply_equiv (v.valuation K), hy'_def]
    simp [hy]

  have hδ_ne : δ_vg ≠ 0 := by
    intro h; rw [h, map_zero] at hδ_emb; exact hd_ne hδ_emb.symm
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact hd_ne hy.symm

  set y'_inv : WithVal (v.valuation K) := (WithVal.equiv (v.valuation K)).symm y⁻¹
  have hδ_unit : IsUnit δ_vg := by
    rw [isUnit_iff_exists_inv]
    use MonoidWithZeroHom.ValueGroup₀.restrict₀
      (@Valued.v (WithVal (v.valuation K)) _ _ _ _) y'_inv
    rw [← map_mul]
    have : y' * y'_inv = 1 := by
      show (WithVal.equiv (v.valuation K)).symm y *
        (WithVal.equiv (v.valuation K)).symm y⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
    rw [this, map_one]
  obtain ⟨δ, hδ⟩ := hδ_unit
  use δ
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢

  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢


  rw [hδ, hδ_emb] at hx

  change @Valued.v (WithVal (w.valuation L)) _ _ _ _ (f x) < M

  rw [hfv]

  exact hd_pow _ hx

theorem completionEmbedding_finite_continuous {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    Continuous (completionEmbedding_finite_ringHom v w) := by


  let g : WithVal (v.valuation K) → WithVal (w.valuation L) :=
    fun x => (WithVal.equiv (w.valuation L)).symm
      (algebraMap K L ((WithVal.equiv (v.valuation K)) x))
  have hg : Continuous g := algebraMap_withVal_continuous v w hw
  have hcoe : Continuous (fun x : WithVal (w.valuation L) => (↑x : w.adicCompletion L)) :=
    (UniformSpace.Completion.uniformContinuous_coe _).continuous
  have heq : (completionEmbedding_finite_ringHom v w : WithVal (v.valuation K) → w.adicCompletion L) =
      (fun x : WithVal (w.valuation L) => (↑x : w.adicCompletion L)) ∘ g := by
    funext x
    simp only [g, completionEmbedding_finite_ringHom, Function.comp, RingHom.coe_comp,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    rfl
  rw [show (↑(completionEmbedding_finite_ringHom v w) :
    WithVal (v.valuation K) → w.adicCompletion L) =
    (fun x : WithVal (w.valuation L) => (↑x : w.adicCompletion L)) ∘ g from heq]
  exact hcoe.comp hg

def completionEmbedding_finite {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    v.adicCompletion K →ₐ[K] w.adicCompletion L :=
  AlgHom.mk'
    (UniformSpace.Completion.extensionHom
      (completionEmbedding_finite_ringHom v w)
      (completionEmbedding_finite_continuous v w hw))
    (fun k x => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      show (UniformSpace.Completion.extensionHom
        (completionEmbedding_finite_ringHom v w)
        (completionEmbedding_finite_continuous v w hw))
        (algebraMap K (v.adicCompletion K) k) =
        algebraMap K (w.adicCompletion L) k
      have : algebraMap K (v.adicCompletion K) k =
        (↑(algebraMap K (WithVal (v.valuation K)) k) : v.adicCompletion K) := rfl
      rw [this, UniformSpace.Completion.extensionHom_coe]
      rfl)

def algebraMapLToAdicCompletion {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    L →ₐ[K] w.adicCompletion L where
  toFun := algebraMap L (w.adicCompletion L)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun _ => rfl

def canonicalMap_finite {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    TensorProduct K L (v.adicCompletion K) →ₐ[K]
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L) :=
  Pi.algHom K
    (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) =>
      w.val.adicCompletion L)
    (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) =>
      Algebra.TensorProduct.productMap
        (algebraMapLToAdicCompletion w.val)
        (completionEmbedding_finite v w.val w.prop))

set_option synthInstance.maxHeartbeats 80000 in

def corollary_13_7_orbit_equiv
    (k K : Type*) [Field k] [Field K] [Algebra k K] [IsGalois k K] :
    Quotient (MulAction.orbitRel (K ≃ₐ[k] K) (NumberField.InfinitePlace K)) ≃
      NumberField.InfinitePlace k :=
  InfinitePlace.orbitRelEquiv

def ComplexEmbedding.conjugateSetoid (L : Type*) [Field L] :
    Setoid (L →+* ℂ) where
  r φ ψ := InfinitePlace.mk φ = InfinitePlace.mk ψ
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

def corollary_13_7_embedding_orbit_equiv_Q (L : Type*) [Field L] :
    Quotient (ComplexEmbedding.conjugateSetoid L) ≃
      NumberField.InfinitePlace L where
  toFun := Quotient.lift InfinitePlace.mk (fun _ _ h => h)
  invFun w := Quotient.mk (ComplexEmbedding.conjugateSetoid L) w.embedding
  left_inv := by
    intro q
    exact Quotient.inductionOn q fun φ => by
      simp only [Quotient.lift_mk]
      exact Quotient.sound (mk_embedding (mk φ))
  right_inv := by
    intro w
    simp only [Quotient.lift_mk]
    exact w.mk_embedding

def EmbeddingsAbove (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) : Type _ :=
  { φ : L →+* ℂ // (InfinitePlace.mk φ).comap (algebraMap K L) = v }

def conjugateSetoidAbove {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    Setoid (EmbeddingsAbove K v (L := L)) where
  r φ ψ := InfinitePlace.mk φ.val = InfinitePlace.mk ψ.val
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

def corollary_13_7_embeddings_equiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    Quotient (conjugateSetoidAbove v (K := K) (L := L)) ≃
      { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v } where
  toFun := Quotient.lift
    (fun (φ : EmbeddingsAbove K v) =>
      (⟨InfinitePlace.mk φ.val, by rw [comap_mk]; exact φ.prop⟩ :
        { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }))
    (fun φ ψ (h : InfinitePlace.mk φ.val = InfinitePlace.mk ψ.val) => by
      simp only [Subtype.mk.injEq]
      exact h)
  invFun w := by
    refine Quotient.mk (conjugateSetoidAbove v) ⟨w.val.embedding, ?_⟩
    rw [comap_mk]
    rw [← comap_mk]
    rw [w.val.mk_embedding]
    exact w.prop
  left_inv := by
    intro q
    exact Quotient.inductionOn q fun ⟨φ, hφ⟩ => by
      simp only [Quotient.lift_mk]
      apply Quotient.sound
      show InfinitePlace.mk (InfinitePlace.mk φ).embedding = InfinitePlace.mk φ
      exact (InfinitePlace.mk φ).mk_embedding
  right_inv := by
    intro ⟨w, hw⟩
    simp only [Quotient.lift_mk, Subtype.mk.injEq]
    exact w.mk_embedding

end GaloisOrbitsAndPlaces

section RealComplexEmbeddings

variable {K : Type*} [Field K]

abbrev IsRealEmbedding (φ : K →+* ℂ) : Prop := ComplexEmbedding.IsReal φ

abbrev IsComplexEmbedding (φ : K →+* ℂ) : Prop := ¬ ComplexEmbedding.IsReal φ
