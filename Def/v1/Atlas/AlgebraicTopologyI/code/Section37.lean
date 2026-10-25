/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section37.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Topology.Compactness.Compact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Comma.Final
import Mathlib.Topology.Separation.Hausdorff
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section37
open CategoryTheory

open CategoryTheory TopologicalSpace Limits


namespace PoincareDuality

universe u

section OpenNhdsColimit

variable {α : Type u} [TopologicalSpace α]

namespace OpenNhdsOfSet

variable {K : Set α}

/-- Forgetful functor `OpenNhdsOfSet K ⥤ (Opens α)ᵒᵖ` sending $U$ to its underlying open
set, contravariantly: the source for Čech-cohomology colimits over neighbourhoods of $K$. -/
def inclusionFunctorOp : OpenNhdsOfSet K ⥤ (Opens α)ᵒᵖ where
  obj U := Opposite.op U.toOpens
  map {_U _V} f := (homOfLE (leOfHom f)).op
  map_id _ := rfl
  map_comp _ _ := rfl

end OpenNhdsOfSet
end OpenNhdsColimit
end PoincareDuality
