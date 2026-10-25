/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part16


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


noncomputable def kwEulerPowerPrefactor (vertexCount edgeCount : Nat) : Complex :=
  (2 : Complex) ^ edgeCount / (2 : Complex) ^ vertexCount


noncomputable def kwLaplacianEdgePrefactor (theta : E -> Real) : Complex :=
  ∏ e : E,
    (Real.cos (theta e) : Complex) / (1 + Real.cos (theta e) : Real)


noncomputable def formanCycleCoefficient (holonomy : Complex) : Complex :=
  2 - holonomy - holonomy⁻¹


noncomputable def formanCRSFCoefficient
    {C : Type*} [Fintype C] (holonomy : C -> Complex) : Complex :=
  ∏ component : C, formanCycleCoefficient (holonomy component)


end StatMech.FrontierA
