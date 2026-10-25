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
set_option autoImplicit false

open scoped Topology Manifold
open MeasureTheory


noncomputable section

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
