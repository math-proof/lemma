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
import Abbrev.v1.Atlas.LieGroups.code.PlancherelCompact.Part2
set_option autoImplicit false

open scoped Topology Manifold
open MeasureTheory


noncomputable section

namespace PlancherelCompact

attribute [instance] IrrFinDimRep.instNormedAddCommGroup
  IrrFinDimRep.instInnerProductSpace IrrFinDimRep.instFiniteDimensional
  IrrFinDimRep.instCompleteSpace IrrFinDimRep.nontrivial

/-- Compact-group Peter-Weyl density for an arbitrary continuous representation. -/
theorem kfinite_dense_in_rep
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (π : ContinuousRep K V) :
    Dense (ContinuousRep.kFiniteSubspace π ⊤ : Set V) := by
  haveI : CompactSpace (⊤ : Subgroup K) := by
    have : IsCompact ((⊤ : Subgroup K) : Set K) := by
      rw [Subgroup.coe_top]
      exact isCompact_univ
    exact isCompact_iff_compactSpace.mp this
  exact ContinuousRep.kFiniteSubspace_dense π ⊤

end PlancherelCompact
end
