module
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.NumberTheory.Padics.WithVal
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part10
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Adeles
public import Def.v1.Atlas.NumberTheoryI.code.LocalFields.Part6
open Metric Filter Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

attribute [instance] IsLocalField.locallyCompact


lemma j_comp_equiv_continuous_of_equiv
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (hequiv : (normAbsValQ j).IsEquiv (Rat.AbsoluteValue.padic p)) :
    Continuous (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom) := by
  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  let e := WithVal.equiv (Rat.padicValuation p)
  let ι := (Rat.castHom ℚ_[p]).comp e.toRingHom
  have hι : IsUniformInducing (ι : WithVal (Rat.padicValuation p) → ℚ_[p]) :=
    Padic.isUniformInducing_cast_withVal
  apply continuous_of_continuousAt_zero
    (j.comp e.toRingHom : WithVal (Rat.padicValuation p) →+ L_v)
  rw [ContinuousAt, map_zero, Filter.tendsto_iff_forall_eventually_mem]
  intro s hs
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hs⟩ := hs
  apply Filter.mem_of_superset
    ((hι.isInducing.continuous).continuousAt.preimage_mem_nhds
      (show Metric.ball 0 (ε ^ c) ∈ nhds (ι 0) by
        rw [map_zero]; exact Metric.ball_mem_nhds 0 (by positivity)))
  intro a ha
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at ha
  apply hs; simp only [Metric.mem_ball, dist_zero_right]
  show ‖j (e a)‖ < ε
  have hpow_a := congr_fun hpow (e a)
  simp only [normAbsValQ, AbsoluteValue.coe_mk, MulHom.coe_mk] at hpow_a
  rw [Rat.AbsoluteValue.padic_eq_padicNorm, ← Padic.eq_padicNorm] at hpow_a
  have h1 : ‖j (e a)‖ ^ c < ε ^ c := by rw [hpow_a]; exact ha
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hc).mp h1

