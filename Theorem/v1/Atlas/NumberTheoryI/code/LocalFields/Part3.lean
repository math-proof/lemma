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
import Def.v1.Atlas.NumberTheoryI.code.LocalFields.Part2
open Metric Filter Set Topology

attribute [instance] IsLocalField.locallyCompact


lemma absValFromNorm_eq_normAbsValQ_castHom
    (L : Type*) [NontriviallyNormedField L] [CharZero L] :
    absValFromNorm L = normAbsValQ (Rat.castHom L) := by
  ext q; simp [absValFromNorm, normAbsValQ]

lemma normAbsValQ_isEquiv_real_uniformContinuous
    {L_v : Type*} [NontriviallyNormedField L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real) :
    UniformContinuous j := by
  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  refine ⟨ε ^ c, by positivity, fun q₁ q₂ hd => ?_⟩
  rw [dist_eq_norm, ← map_sub]
  have key : ‖j (q₁ - q₂)‖ ^ c = Rat.AbsoluteValue.real (q₁ - q₂) := congr_fun hpow (q₁ - q₂)
  have hdist : dist q₁ q₂ = Rat.AbsoluteValue.real (q₁ - q₂) := by
    rw [Rat.AbsoluteValue.real_eq_abs, Rat.dist_eq]; push_cast; rfl
  have h2 : ‖j (q₁ - q₂)‖ ^ c < ε ^ c := by rw [key]; linarith [hdist]
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hc).mp h2

