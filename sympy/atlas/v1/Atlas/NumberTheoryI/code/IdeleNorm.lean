/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdeleNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.Ideles
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ideles
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import sympy.atlas.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra
import sympy.atlas.v1.Atlas.NumberTheoryI.code.KroneckerWeber

noncomputable section

open NumberField IsDedekindDomain Ideles

def InfinitePlace.localNormHom {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : InfinitePlace L) (v : InfinitePlace K) :
    w.Completion →* v.Completion := by
  classical
  exact
    if hv : v.IsReal then
      if hw : w.IsReal then

        (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom.comp
          (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMonoidHom
      else

        (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom.comp
          (Complex.normSq.toMonoidHom.comp
            (InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (InfinitePlace.not_isReal_iff_isComplex.mp hw)).toMonoidHom)
    else
      if hw : w.IsReal then

        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).symm.toMonoidHom.comp
          (Complex.ofRealHom.toMonoidHom.comp
            (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMonoidHom)
      else

        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).symm.toMonoidHom.comp
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).toMonoidHom

open Classical in
def infiniteNormComponent (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : InfinitePlace K) :
    InfiniteAdeleRing L →* v.Completion where
  toFun b := ∏ w : InfinitePlace L,
    if w.comap (algebraMap K L) = v then
      InfinitePlace.localNormHom w v (b w)
    else 1
  map_one' := by
    apply Finset.prod_eq_one
    intro w _
    split_ifs with h
    · exact (InfinitePlace.localNormHom w v).map_one
    · rfl
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    congr 1
    ext w
    split_ifs with h
    · exact (InfinitePlace.localNormHom w v).map_mul _ _
    · exact (mul_one 1).symm

def infiniteAdeleNormHom (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    InfiniteAdeleRing L →* InfiniteAdeleRing K :=
  Pi.monoidHom (fun v => infiniteNormComponent K L v)

def HeightOneSpectrum.adicCompletionAlgebra {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K))
    (hw : v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal) :
    Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  instAlgebraAdicCompletionOfLiesOver K v w hw

def HeightOneSpectrum.localNormHom {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K))
    (hw : v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal) :
    (w.adicCompletion L →* v.adicCompletion K) :=
  letI := HeightOneSpectrum.adicCompletionAlgebra w v hw
  Algebra.norm (v.adicCompletion K)

theorem HeightOneSpectrum.localNormHom_mem_integers {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K))
    (hw : v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal)
    (x : w.adicCompletion L) (hx : x ∈ w.adicCompletionIntegers L) :
    HeightOneSpectrum.localNormHom w v hw x ∈ v.adicCompletionIntegers K := by

  letI alg_KL := HeightOneSpectrum.adicCompletionAlgebra w v hw

  letI alg_OO : Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
    KroneckerWeber.prop_8_11_completion_integers_algebra (𝓞 K) K L (𝓞 L) v w hw

  letI alg_OL : Algebra (v.adicCompletionIntegers K) (w.adicCompletion L) :=
    ((algebraMap (v.adicCompletion K) (w.adicCompletion L)).comp
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).toAlgebra

  haveI : IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) (w.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  unfold HeightOneSpectrum.localNormHom

  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx

  set x' : (w.adicCompletionIntegers L) := ⟨x, hx⟩

  haveI := isScalarTower_adicCompletion (L := L) K v w hw

  haveI : Module.Finite (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
    KroneckerWeber.adicCompletionIntegers_module_finite (K := K) (L := L) v w (fun _ => rfl)


  have hint : IsIntegral (v.adicCompletionIntegers K) x' :=
    isIntegral_of_noetherian
      (isNoetherian_of_isNoetherianRing_of_finite (v.adicCompletionIntegers K)
        (w.adicCompletionIntegers L)) x'


  haveI : IsScalarTower (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) (w.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      show (algebraMap (v.adicCompletion K) (w.adicCompletion L))
        ((algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) r) =
        (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L))
          ((algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) r)


      change (algebraMap (v.adicCompletion K) (w.adicCompletion L)) r.val =
        ((algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) r).val


      rfl)
  have hint2 : IsIntegral (v.adicCompletionIntegers K) x := by
    have h := hint.algebraMap (B := w.adicCompletion L)
    convert h using 1

  have hint3 : IsIntegral (v.adicCompletionIntegers K) (Algebra.norm (v.adicCompletion K) x) :=
    Algebra.isIntegral_norm (v.adicCompletion K) hint2

  rw [IsIntegrallyClosed.isIntegral_iff] at hint3
  obtain ⟨y, hy⟩ := hint3
  rw [← hy]
  exact y.property

theorem HeightOneSpectrum.finite_placesAbove {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Set.Finite ({w : HeightOneSpectrum (𝓞 L) | w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal}) := by
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
    NumberField.RingOfIntegers.algebraMap.injective K L
  have hv_ne : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ 0 := by
    intro h
    apply v.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have hxm : algebraMap (𝓞 K) (𝓞 L) x ∈ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal :=
      Ideal.mem_map_of_mem _ hx
    rw [h] at hxm
    change algebraMap (𝓞 K) (𝓞 L) x ∈ (⊥ : Ideal (𝓞 L)) at hxm
    rw [Ideal.mem_bot] at hxm
    have : x = 0 := hinj (by rw [hxm, map_zero])
    exact this ▸ Ideal.zero_mem _
  apply Set.Finite.subset (Ideal.finite_factors hv_ne)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  exact Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr (hw ▸ le_refl _))

def HeightOneSpectrum.placesAbove {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K)) : Finset (HeightOneSpectrum (𝓞 L)) :=
  (HeightOneSpectrum.finite_placesAbove v).toFinset

lemma HeightOneSpectrum.liesOver_of_mem_placesAbove {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∈ HeightOneSpectrum.placesAbove v (L := L)) :
    v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal := by
  have hmem := (HeightOneSpectrum.finite_placesAbove v).mem_toFinset.mp hw
  simp only [Set.mem_setOf_eq] at hmem
  exact hmem ▸ le_refl _

def finiteNormComponent (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    FiniteAdeleRing (𝓞 L) L →* v.adicCompletion K where
  toFun b := (HeightOneSpectrum.placesAbove v (L := L)).attach.prod fun w =>
    HeightOneSpectrum.localNormHom w.1 v
      (HeightOneSpectrum.liesOver_of_mem_placesAbove w.2) (b w.1)
  map_one' := by
    apply Finset.prod_eq_one
    intro w _
    exact (HeightOneSpectrum.localNormHom w.1 v
      (HeightOneSpectrum.liesOver_of_mem_placesAbove w.2)).map_one
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    congr 1
    ext w
    exact (HeightOneSpectrum.localNormHom w.1 v
      (HeightOneSpectrum.liesOver_of_mem_placesAbove w.2)).map_mul _ _

theorem finiteNormComponent_mem_integers_almost_all (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (b : FiniteAdeleRing (𝓞 L) L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (finiteNormComponent K L v) b ∈ v.adicCompletionIntegers K := by

  have hb := b.2
  rw [Filter.Eventually, Filter.mem_cofinite] at hb ⊢

  have hgood : ∀ v : HeightOneSpectrum (𝓞 K),
      (∀ w ∈ HeightOneSpectrum.placesAbove v (L := L),
        b w ∈ w.adicCompletionIntegers L) →
      finiteNormComponent K L v b ∈ v.adicCompletionIntegers K := by
    intro v hv_int
    simp only [finiteNormComponent, MonoidHom.coe_mk, OneHom.coe_mk]
    apply (v.adicCompletionIntegers K).prod_mem
    intro ⟨w, hw_mem⟩ _
    exact HeightOneSpectrum.localNormHom_mem_integers w v
      (HeightOneSpectrum.liesOver_of_mem_placesAbove hw_mem) (b w) (hv_int w hw_mem)


  let underMap : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 K) := fun w =>
    ⟨w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)),
     Ideal.comap_isPrime _ w.asIdeal,
     Ideal.IsIntegralClosure.comap_ne_bot L w.ne_bot⟩

  apply Set.Finite.subset (hb.image underMap)
  intro v hv
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hv

  have : ¬ ∀ w ∈ HeightOneSpectrum.placesAbove v (L := L),
      (b : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) w ∈
        w.adicCompletionIntegers L := by
    intro h_all
    exact hv (hgood v h_all)
  push Not at this
  obtain ⟨w, hw_mem, hw_bad⟩ := this
  refine ⟨w, ?_, ?_⟩
  ·
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    exact hw_bad
  ·
    have hmem := (HeightOneSpectrum.finite_placesAbove v).mem_toFinset.mp hw_mem
    simp only [Set.mem_setOf_eq] at hmem
    exact HeightOneSpectrum.ext hmem

def finiteAdeleNormHom (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    FiniteAdeleRing (𝓞 L) L →* FiniteAdeleRing (𝓞 K) K where
  toFun b := ⟨fun v => finiteNormComponent K L v b,
    finiteNormComponent_mem_integers_almost_all K L b⟩
  map_one' := Subtype.ext <| funext fun v => (finiteNormComponent K L v).map_one
  map_mul' b₁ b₂ := Subtype.ext <| funext fun v => (finiteNormComponent K L v).map_mul b₁ b₂

def adeleNormHom (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    NumberField.AdeleRing (𝓞 L) L →* NumberField.AdeleRing (𝓞 K) K :=
  MonoidHom.prodMap (infiniteAdeleNormHom K L) (finiteAdeleNormHom K L)

def ideleNorm (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    IdeleGroup L →* IdeleGroup K :=
  Units.map (adeleNormHom K L)

set_option maxHeartbeats 1600000 in
end
