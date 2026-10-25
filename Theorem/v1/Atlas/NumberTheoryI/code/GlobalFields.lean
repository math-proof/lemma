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
import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Def.v1.Atlas.NumberTheoryI.code.GlobalFields.Part4


noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

section TensorProductDecomposition

set_option maxHeartbeats 2000000

set_option synthInstance.maxHeartbeats 80000

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

end TensorProductDecomposition
end
