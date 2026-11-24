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
public import Theorem.v1.Atlas.LieGroups.code.PlancherelCompact
set_option autoImplicit false
open scoped Topology Manifold
open MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace PlancherelCompact

attribute [instance] IrrFinDimRep.instNormedAddCommGroup
  IrrFinDimRep.instInnerProductSpace IrrFinDimRep.instFiniteDimensional
  IrrFinDimRep.instCompleteSpace IrrFinDimRep.nontrivial

/-- Alias: ContinuousMap notation C(G, R) is Mathlib; exposed for atlas wrappers. -/
abbrev ContMapReal (G : Type*) [TopologicalSpace G] := C(G, ℝ)

abbrev ContMapComplex (G : Type*) [TopologicalSpace G] := C(G, ℂ)

end PlancherelCompact
end
