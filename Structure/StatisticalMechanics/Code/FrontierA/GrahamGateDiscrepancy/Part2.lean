/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part8


namespace StatMech.FrontierA

structure RelationPartialMatching.HoleState
    {A B : Type*} [Fintype A] (r : A -> B -> Prop) where
  matching : RelationPartialMatching r
  maximum : matching.IsMaximum
  hole : A
  hole_unmatched : hole ∉ matching.support

end StatMech.FrontierA
