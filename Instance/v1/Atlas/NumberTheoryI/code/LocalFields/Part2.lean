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
import Def.v1.Atlas.NumberTheoryI.code.LocalFields.Part8
open Metric Filter Set Topology

attribute [instance] IsLocalField.locallyCompact


noncomputable instance LaurentSeries.instIsRankOneDiscrete (K : Type*) [Field K] :
    Valuation.IsRankOneDiscrete (LaurentSeries.valued K).v := by
  change Valuation.IsRankOneDiscrete ((PowerSeries.idealX K).valuation (LaurentSeries K))
  have h : PowerSeries.idealX K = IsDiscreteValuationRing.maximalIdeal (PowerSeries K) := by
    ext : 1
    simp only [PowerSeries.idealX, IsDiscreteValuationRing.maximalIdeal]
    exact PowerSeries.maximalIdeal_eq_span_X.symm
  rw [h]; infer_instance

@[reducible]
noncomputable instance LaurentSeries.instRankOne (K : Type*) [Field K] :
    Valuation.RankOne (LaurentSeries.valued K).v :=
  Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)

section NumberFieldCompletions

open NumberField NumberField.InfinitePlace.Completion IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

noncomputable instance NumberField.InfinitePlace.Completion.instIsLocalField
    (v : NumberField.InfinitePlace K) : IsLocalField v.Completion where
  locallyCompact := inferInstance

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
noncomputable instance HeightOneSpectrum.adicCompletion.instIsLocalField
    (v : HeightOneSpectrum (𝓞 K)) : IsLocalField (v.adicCompletion K) := by
  open scoped Valued in
  haveI : Empty.Finite (Valued.ResidueField (v.adicCompletion K)) :=
    NumberField.Adeles.adicCompletion_finite_residueField K v
  open scoped Valued in
  haveI : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  haveI : CompleteSpace (v.adicCompletion K) := inferInstance
  open scoped Valued in
  haveI : ProperSpace (v.adicCompletion K) :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  exact { locallyCompact := inferInstance }

end NumberFieldCompletions
