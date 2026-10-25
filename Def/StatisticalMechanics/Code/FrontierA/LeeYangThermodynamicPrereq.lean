/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangThermodynamicPrereq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangBoxPressure.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangThermodynamicPrereq
open scoped BigOperators
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FK StatMech.FrontierB StatMech.FrontierC
  StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def leeYangRightHalfPlaneDerivativeBound
    (beta : ℝ) (h : ℂ) : ℝ :=
  beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ /
    (1 - ‖Complex.exp (-2 * (beta : ℂ) * h)‖)

noncomputable def leeYangLeftHalfPlaneDerivativeBound
    (beta : ℝ) (h : ℂ) : ℝ :=
  beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ /
    (‖Complex.exp (-2 * (beta : ℂ) * h)‖ - 1)

end StatMech.FrontierA
