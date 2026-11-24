module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
public import Def.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part5
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

theorem jbc_csq_inj : Function.Injective jbc_csq := by decide +kernel


theorem jbc_csq_y (i : Fin 4) : (jbc_csq i) 1 = 0 ∨ (jbc_csq i) 1 = 1 := by
  fin_cases i <;> simp [jbc_csq]


end Lattice
end StatMech
