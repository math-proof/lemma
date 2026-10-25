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
import Def.v1.Atlas.NumberTheoryI.code.LocalFields.Part5
open Metric Filter Set Topology

attribute [instance] IsLocalField.locallyCompact


lemma normAbsValQ_isEquiv_real_eq
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real)
    (hnorm_2 : ‖j (2 : ℚ)‖ = 2) :
    normAbsValQ j = Rat.AbsoluteValue.real := by

  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  have hpow_fun : ∀ q : ℚ, (normAbsValQ j q) ^ c = (Rat.AbsoluteValue.real) q :=
    fun q => congr_fun hpow q

  have h2_val : normAbsValQ j (2 : ℚ) = (2 : ℝ) := hnorm_2
  have h2_real : (Rat.AbsoluteValue.real) (2 : ℚ) = (2 : ℝ) := by
    rw [Rat.AbsoluteValue.real_eq_abs]; norm_num
  have h2c : (2 : ℝ) ^ c = (2 : ℝ) := by
    specialize hpow_fun (2 : ℚ); rw [h2_val, h2_real] at hpow_fun; exact hpow_fun
  have hc_eq : c = 1 := by
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have h1 := congr_arg Real.log h2c
    rw [Real.log_rpow h2pos] at h1
    have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have : c * Real.log 2 = 1 * Real.log 2 := by linarith
    exact mul_right_cancel₀ (ne_of_gt hlog2_pos) this

  ext q
  have := hpow_fun q
  rw [hc_eq, Real.rpow_one] at this
  exact this

