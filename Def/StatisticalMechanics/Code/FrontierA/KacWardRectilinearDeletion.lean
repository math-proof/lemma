/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearGraphCancellation
import Theorem.StatisticalMechanics.Code.Onsager.StateWeightedDeletion
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearDeletion
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

noncomputable def kwScaleGraphEdgeWeight
    {V : Type*} [DecidableEq V]
    (weight : Sym2 V -> ℂ) (edge : Sym2 V) (t : ℂ) :
    Sym2 V -> ℂ :=
  fun other => if other = edge then t * weight other else weight other


end StatMech.FrontierA
