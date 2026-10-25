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
import Def.v1.Atlas.NumberTheoryI.code.LocalFields.Part7
open Metric Filter Set Topology

attribute [instance] IsLocalField.locallyCompact


lemma extendRingHom_padic_of_equiv_continuous
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (hequiv : (normAbsValQ j).IsEquiv (Rat.AbsoluteValue.padic p)) :
    Continuous (extendRingHom_padic_of_equiv j p hequiv) := by
  show Continuous (fun x : ℚ_[p] =>
    (UniformSpace.Completion.extensionHom
      (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)
      (j_comp_equiv_continuous_of_equiv j p hequiv))
      (Padic.withValRingEquiv.symm x))
  exact Continuous.comp
    (show Continuous (UniformSpace.Completion.extension
      (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)) from
      UniformSpace.Completion.continuous_extension)
    Padic.withValUniformEquiv.symm.continuous

