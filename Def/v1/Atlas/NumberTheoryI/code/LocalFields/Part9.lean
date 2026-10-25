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
import Instance.v1.Atlas.NumberTheoryI.code.LocalFields.Part2
open Metric Filter Set Topology

attribute [instance] IsLocalField.locallyCompact


section NumberFieldCompletions

open NumberField NumberField.InfinitePlace.Completion IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

noncomputable def numberFieldCompletion_isLocalField
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K)) :
    match v with
    | Sum.inl w => IsLocalField w.Completion
    | Sum.inr p => IsLocalField (p.adicCompletion K) :=
  match v with
  | Sum.inl w => NumberField.InfinitePlace.Completion.instIsLocalField w
  | Sum.inr p => HeightOneSpectrum.adicCompletion.instIsLocalField p

noncomputable def corollary_9_7
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K)) :
    match v with
    | Sum.inl w => IsLocalField w.Completion
    | Sum.inr p => IsLocalField (p.adicCompletion K) :=
  numberFieldCompletion_isLocalField v

@[reducible] noncomputable def numberFieldCompletion_isLocalField_infinite
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    IsLocalField v.Completion :=
  NumberField.InfinitePlace.Completion.instIsLocalField v

@[reducible] noncomputable def corollary_9_7_infinite_place
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    IsLocalField v.Completion :=
  numberFieldCompletion_isLocalField_infinite v

@[reducible] noncomputable def numberFieldCompletion_isLocalField_finite
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsLocalField (v.adicCompletion K) :=
  HeightOneSpectrum.adicCompletion.instIsLocalField v

@[reducible] noncomputable def corollary_9_7_finite_place
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsLocalField (v.adicCompletion K) :=
  numberFieldCompletion_isLocalField_finite v

end NumberFieldCompletions
