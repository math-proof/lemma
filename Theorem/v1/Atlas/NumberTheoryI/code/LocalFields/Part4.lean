/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.NumberTheory.Ostrowski
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part10
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Adeles
import Def.v1.Atlas.NumberTheoryI.code.LocalFields.Part3
open Metric Filter Set Topology

attribute [instance] IsLocalField.locallyCompact


lemma extendRingHom_real_continuous
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real) :
    Continuous (extendRingHom_real j hequiv) :=
  (uniformContinuous_uniformly_extend
    Rat.isUniformEmbedding_coe_real.isUniformInducing
    Rat.isDenseEmbedding_coe_real.dense
    (normAbsValQ_isEquiv_real_uniformContinuous j hequiv)).continuous

lemma extendRingHom_real_extends
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real)
    (q : ℚ) : extendRingHom_real j hequiv (q : ℝ) = j q :=
  IsDenseInducing.extend_eq
    (Rat.isUniformEmbedding_coe_real.isUniformInducing.isDenseInducing
      Rat.isDenseEmbedding_coe_real.dense)
    (normAbsValQ_isEquiv_real_uniformContinuous j hequiv).continuous q

lemma normAbsValQ_isEquiv_padic_eq
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (hequiv : (normAbsValQ j).IsEquiv (Rat.AbsoluteValue.padic p))
    (hnorm_p : ‖j (↑p : ℚ)‖ = (↑p : ℝ)⁻¹) :
    normAbsValQ j = Rat.AbsoluteValue.padic p := by

  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  have hpow_fun : ∀ q : ℚ, (normAbsValQ j q) ^ c = (Rat.AbsoluteValue.padic p) q :=
    fun q => congr_fun hpow q

  have hp_val : normAbsValQ j (↑p : ℚ) = (↑p : ℝ)⁻¹ := hnorm_p
  have hp_padic : (Rat.AbsoluteValue.padic p) (↑p : ℚ) = (↑p : ℝ)⁻¹ := by
    rw [Rat.AbsoluteValue.padic_eq_padicNorm]
    simp [padicNorm.padicNorm_p_of_prime]
  have hpc : ((↑p : ℝ)⁻¹) ^ c = (↑p : ℝ)⁻¹ := by
    specialize hpow_fun (↑p : ℚ); rw [hp_val, hp_padic] at hpow_fun; exact hpow_fun
  have hp_pos : (0 : ℝ) < (↑p : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p))
  have hp_lt_one : (↑p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; right; exact_mod_cast Nat.Prime.one_lt (Fact.out : Nat.Prime p)
  have hc_eq : c = 1 := by
    have hlog_neg := Real.log_neg hp_pos hp_lt_one
    have := congr_arg Real.log hpc
    rw [Real.log_rpow hp_pos] at this
    nlinarith

  ext q
  have := hpow_fun q
  rw [hc_eq, Real.rpow_one] at this
  exact this

lemma j_comp_equiv_continuous
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (heq : normAbsValQ j = Rat.AbsoluteValue.padic p) :
    Continuous (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom) := by
  let e := WithVal.equiv (Rat.padicValuation p)
  let ι := (Rat.castHom ℚ_[p]).comp e.toRingHom
  have hι : IsUniformInducing (ι : WithVal (Rat.padicValuation p) → ℚ_[p]) :=
    Padic.isUniformInducing_cast_withVal
  have hfι : ∀ a : WithVal (Rat.padicValuation p),
      ‖j.comp e.toRingHom a‖ = ‖ι a‖ := by
    intro a; show ‖j (e a)‖ = ‖(↑(e a) : ℚ_[p])‖
    have h1 : normAbsValQ j (e a) = Rat.AbsoluteValue.padic p (e a) := by rw [heq]
    simp only [normAbsValQ, AbsoluteValue.coe_mk, MulHom.coe_mk, Rat.AbsoluteValue.padic] at h1
    rw [h1, Padic.eq_padicNorm]
  apply continuous_of_continuousAt_zero (j.comp e.toRingHom : WithVal (Rat.padicValuation p) →+ L_v)
  rw [ContinuousAt, map_zero, Filter.tendsto_iff_forall_eventually_mem]
  intro s hs; rw [Metric.mem_nhds_iff] at hs; obtain ⟨ε, hε, hs⟩ := hs
  apply Filter.mem_of_superset
    ((hι.isInducing.continuous).continuousAt.preimage_mem_nhds
      (show Metric.ball 0 ε ∈ nhds (ι 0) by rw [map_zero]; exact Metric.ball_mem_nhds 0 hε))
  intro a ha; simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at ha
  apply hs; simp only [Metric.mem_ball, dist_zero_right]
  show ‖j.comp e.toRingHom a‖ < ε; rw [hfι]; exact ha

