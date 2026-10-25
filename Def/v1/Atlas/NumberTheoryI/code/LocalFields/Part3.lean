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
import Theorem.v1.Atlas.NumberTheoryI.code.LocalFields.Part3
open Metric Filter Set Topology

attribute [instance] IsLocalField.locallyCompact


noncomputable def extendRingHom_real
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real) :
    ℝ →+* L_v :=
  @IsDenseInducing.extendRingHom ℚ _ _ ℝ _ _ _ L_v _ _ _ _ _
    (Rat.castHom ℝ) j
    Rat.isUniformEmbedding_coe_real.isUniformInducing
    Rat.isDenseEmbedding_coe_real.dense
    (normAbsValQ_isEquiv_real_uniformContinuous j hequiv)

