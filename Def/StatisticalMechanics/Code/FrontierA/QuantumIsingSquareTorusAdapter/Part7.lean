/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter.Part6
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


noncomputable def quantumIsingSquareTorusTanhWeight
    (beta h : Real) (L : Nat) :
    Sym2 (ZMod L × ZMod L) → Real :=
  fun edge ↦ if squareTorusHorizontalEdge L edge then
    Real.tanh (beta / (4 * L))
  else Real.tanh (quantumIsingVerticalCoupling beta h L)

end StatMech.FrontierA
