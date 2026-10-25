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
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part13


namespace StatMech.FrontierA

noncomputable def finiteRelationNeighborhood
    {A : Type*} [Fintype A] (R : A -> A -> Prop) (S : Finset A) :
    Finset A := by
  classical
  exact Finset.univ.filter fun y => ∃ x ∈ S, R x y


noncomputable def finiteCommonClosureStep
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) : Finset A := by
  classical
  exact S ∪ (finiteRelationNeighborhood R S).filter fun y => P y ∧ Q y

end StatMech.FrontierA
