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
import Theorem.v1.Atlas.NumberTheoryI.code.LocalFields
open Metric Filter Set Topology

attribute [instance] IsLocalField.locallyCompact


noncomputable def absValFromNorm (L : Type*) [NormedField L] [CharZero L] :
    AbsoluteValue ℚ ℝ where
  toFun q := ‖(q : L)‖
  map_mul' x y := by simp [norm_mul]
  nonneg' x := norm_nonneg _
  eq_zero' x := by
    simp only [norm_eq_zero]; constructor
    · intro h; exact_mod_cast h
    · intro h; simp [h]
  add_le' x y := by
    show ‖((x + y : ℚ) : L)‖ ≤ ‖(x : L)‖ + ‖(y : L)‖
    rw [show ((x + y : ℚ) : L) = (x : L) + (y : L) from by push_cast; ring]
    exact norm_add_le _ _

