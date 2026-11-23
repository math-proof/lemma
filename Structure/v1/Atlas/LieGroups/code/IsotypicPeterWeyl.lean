/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/IsotypicPeterWeyl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Def.v1.Atlas.LieGroups.code.IsotypicPeterWeyl


public noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

section IrrK

structure IrrFinDimRep (K : Type*) [Group K] [TopologicalSpace K]
    [CompactSpace K] where
  carrier : Type
  [instNACG : NormedAddCommGroup carrier]
  [instIPS : InnerProductSpace ℂ carrier]
  [instFD : FiniteDimensional ℂ carrier]
  [instCS : CompleteSpace carrier]
  rep : ContinuousRep K carrier
  irred : rep.IsIrreducible
  unitary : rep.IsUnitary
  [instNT : Nontrivial carrier]

end IrrK
end ContinuousRep
end
