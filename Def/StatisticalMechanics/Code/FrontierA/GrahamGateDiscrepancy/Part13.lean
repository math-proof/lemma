module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Max
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part14


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def finiteCommonClosureIter
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) : Nat -> Finset A
  | 0 => S
  | n + 1 => finiteCommonClosureStep P Q R
      (finiteCommonClosureIter P Q R S n)

end StatMech.FrontierA
