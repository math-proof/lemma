module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGauge
public import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
public import Mathlib.Algebra.Ring.GeomSum
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part2
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAcyclicElimination.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open Matrix


noncomputable def kwInternalGadgetTransition
    {External Internal : Type*}
    [Fintype External] [DecidableEq External]
    [Fintype Internal] [DecidableEq Internal]
    (external : Matrix External External ℂ)
    (enter : Matrix External Internal ℂ)
    (exit : Matrix Internal External ℂ)
    (internal : Matrix Internal Internal ℂ) :
    Matrix (External ⊕ Internal) (External ⊕ Internal) ℂ :=
  Matrix.fromBlocks external enter exit internal


noncomputable def kwEliminateAcyclicInternal
    {External Internal : Type*}
    [Fintype External] [DecidableEq External]
    [Fintype Internal] [DecidableEq Internal]
    (external : Matrix External External ℂ)
    (enter : Matrix External Internal ℂ)
    (exit : Matrix Internal External ℂ)
    (internal : Matrix Internal Internal ℂ)
    (nilpotenceIndex : ℕ) : Matrix External External ℂ :=
  external + enter * kwNilpotentResolvent internal nilpotenceIndex * exit

end StatMech.FrontierA
