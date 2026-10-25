/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part3


namespace StatMech.FrontierA

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def disjointCoordinatePairs (E : Type*) [Fintype E] :
    Finset (Set E × Set E) := by
  classical
  exact Finset.univ.filter fun pair => Disjoint pair.1 pair.2

end StatMech.FrontierA
