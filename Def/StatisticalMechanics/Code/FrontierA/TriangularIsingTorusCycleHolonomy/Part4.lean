/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSurfaceTwist
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open scoped Affine


noncomputable def triangularIntSimplePolygon
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hclosed : ∑ i, triangularIntStep (direction i) = 0)
    (hn : 3 ≤ n) (hinjective : Function.Injective (triangularIntPos direction)) :
    KWFiniteSimplePolygon n where
  vertex := fun i => triangularIntPoint (triangularIntPos direction i)
  three_le := hn
  vertex_injective := triangularIntPoint_injective.comp hinjective
  vertex_not_strictly_between :=
    triangularIntPos_vertex_not_strictly_between direction hclosed hinjective
  edgeInteriors_disjoint :=
    triangularIntPos_edgeInteriors_disjoint direction hclosed hn hinjective


noncomputable def triangularTorusGraphDartDirection
    (L : Nat) [Fact (2 < L)]
    (d : (triangularTorusGraph L).Dart) : Fin 6 :=
  ((triangularTorusDartEquiv L).symm d).2


end StatMech.FrontierA
