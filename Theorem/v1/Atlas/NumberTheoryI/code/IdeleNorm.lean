/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdeleNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.Ideles.Part3
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ideles
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Def.v1.Atlas.NumberTheoryI.code.IdeleNorm


noncomputable section

open NumberField IsDedekindDomain Ideles

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

end
