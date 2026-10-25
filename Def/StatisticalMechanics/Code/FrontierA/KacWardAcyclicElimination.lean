/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAcyclicElimination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGauge
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
import Mathlib.Algebra.Ring.GeomSum
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix


noncomputable def kwNilpotentResolvent
    {Internal : Type*} [Fintype Internal] [DecidableEq Internal]
    (internal : Matrix Internal Internal ℂ) (nilpotenceIndex : ℕ) :
    Matrix Internal Internal ℂ :=
  ∑ k ∈ Finset.range nilpotenceIndex, internal ^ k

end StatMech.FrontierA
