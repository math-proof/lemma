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
public import Theorem.v1.Atlas.NumberTheoryI.code.LocalFields
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

