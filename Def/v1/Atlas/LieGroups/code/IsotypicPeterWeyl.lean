module
public import Def.v1.Atlas.LieGroups.code.KFinite.Part3
public import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
public import Theorem.Complex.IsKFinite0
public import Def.v1.Atlas.LieGroups.code.KFiniteProps.Part4
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/IsotypicPeterWeyl.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

section IsotypicHomDef

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

variable [IsTopologicalGroup G]

def IsotypicComponentHom
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (π : ContinuousRep G V) (K : Subgroup G)
    (σ : ContinuousRep K Wσ) :
    Submodule ℂ V :=
  ⨆ (T : RepHom σ (π.restrictSubgroup K)),
    LinearMap.range T.toContinuousLinearMap.toLinearMap

def isotypicEvaluation
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (π : ContinuousRep G V) (K : Subgroup G)
    (σ : ContinuousRep K Wσ)
    (T : RepHom σ (π.restrictSubgroup K)) (u : Wσ) : V :=
  T.toContinuousLinearMap u

end IsotypicHomDef

section MatrixCoefficients

variable (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

def matrixCoefficient
    {Wρ : Type*} [AddCommGroup Wρ] [Module ℂ Wρ] [TopologicalSpace Wρ]
    (ρ : ContinuousRep K Wρ) (φ : Wρ →L[ℂ] ℂ) (v : Wρ) :
    K → ℂ :=
  fun g => φ ((ρ.toMonoidHom g) v)

def MatrixCoefficientSubspace
    {Wρ : Type*} [AddCommGroup Wρ] [Module ℂ Wρ] [TopologicalSpace Wρ]
    (ρ : ContinuousRep K Wρ) :
    Submodule ℂ (K → ℂ) :=
  Submodule.span ℂ { f : K → ℂ | ∃ (φ : Wρ →L[ℂ] ℂ) (v : Wρ), f = matrixCoefficient K ρ φ v }

end MatrixCoefficients
end ContinuousRep
end
