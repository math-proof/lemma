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
public import Structure.v1.Atlas.LieGroups.code.IsotypicPeterWeyl


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

section IrrK

attribute [instance] IrrFinDimRep.instNACG IrrFinDimRep.instIPS
  IrrFinDimRep.instFD IrrFinDimRep.instCS IrrFinDimRep.instNT

def IrrFinDimRep.dim {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] (ρ : IrrFinDimRep K) : ℕ :=
  Module.finrank ℂ ρ.carrier

end IrrK
end ContinuousRep
end
