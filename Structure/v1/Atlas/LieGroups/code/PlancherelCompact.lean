/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
public import Theorem.Complex.IsStronglyContinuousToMonoidHom
public import Theorem.Complex.IsKFinite0
public import Theorem.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
public import Theorem.Real.IsSmoothVector0
public import Theorem.Complex.Eq_Sum_Mul
public import Def.v1.Atlas.LieGroups.code.KFinite.Part3
public import Def.v1.Atlas.LieGroups.code.SmoothVectors
public import Def.v1.Atlas.LieGroups.code.KFiniteProps.Part4
public import Def.v1.Atlas.LieGroups.code.IsotypicPeterWeyl.Part3
public import Theorem.v1.Atlas.LieGroups.code.SmoothVectorsProps
public import Def.v1.Atlas.LieGroups.code.CompactMeasures
set_option autoImplicit false

open scoped Topology Manifold
open MeasureTheory


public noncomputable section

namespace PlancherelCompact

structure IrrFinDimRep (K : Type*) [Group K] [TopologicalSpace K]
    [CompactSpace K] where
  carrier : Type
  [instNormedAddCommGroup : NormedAddCommGroup carrier]
  [instInnerProductSpace : InnerProductSpace ℂ carrier]
  [instFiniteDimensional : FiniteDimensional ℂ carrier]
  [instCompleteSpace : CompleteSpace carrier]
  rep : ContinuousRep K carrier
  irred : rep.IsIrreducible
  unitary : rep.IsUnitary
  [nontrivial : Nontrivial carrier]

end PlancherelCompact
end
