/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part2
open Finset


namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem finiteBipartiteRelationNeighborhood_mono
    {A : Type u} {B : Type v} [Fintype B]
    (related : A -> B -> Prop) :
    Monotone (finiteBipartiteRelationNeighborhood related) := by
  classical
  intro smaller larger hsubset token htoken
  obtain ⟨source, hsource, hrelated⟩ :=
    (Finset.mem_filter.mp htoken).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ token,
    source, hsubset hsource, hrelated⟩


end StatMech.GrahamGHS.FourColor
