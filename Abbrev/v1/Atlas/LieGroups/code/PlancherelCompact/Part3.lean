/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import Lemma.Complex.IsKFinite0
import Lemma.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
import Lemma.Real.IsSmoothVector0
import Lemma.Complex.Eq_Sum_Mul
import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Def.v1.Atlas.LieGroups.code.SmoothVectors
import Def.v1.Atlas.LieGroups.code.KFiniteProps.Part4
import Def.v1.Atlas.LieGroups.code.IsotypicPeterWeyl.Part3
import Theorem.v1.Atlas.LieGroups.code.SmoothVectorsProps
import Def.v1.Atlas.LieGroups.code.CompactMeasures
import Theorem.v1.Atlas.LieGroups.code.PlancherelCompact
set_option autoImplicit false

open scoped Topology Manifold
open MeasureTheory


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
