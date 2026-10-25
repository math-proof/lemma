/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodic2D
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol
open scoped BigOperators
open MeasureTheory


namespace StatMech.FrontierA

noncomputable def triangularIsingFreeEnergyValue (J1 J2 J3 : ℝ) : ℝ :=
  -Real.log 2 - (1 / (8 * Real.pi ^ 2)) *
    ∫ k1 in (-Real.pi)..Real.pi,
      ∫ k2 in (-Real.pi)..Real.pi,
        Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)

end StatMech.FrontierA
