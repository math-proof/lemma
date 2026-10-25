/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordEndpointOrder


namespace StatMech.FrontierA

noncomputable def kwChordBoundaryTurnDiscrepancy
    (a b c d chord : ℂ) : ℝ :=
  (((Complex.arg b : Real.Angle) -
          (Complex.arg a : Real.Angle)).toReal +
      ((Complex.arg d : Real.Angle) -
          (Complex.arg c : Real.Angle)).toReal) -
    ((((Complex.arg (-chord) : Real.Angle) -
            (Complex.arg a : Real.Angle)).toReal +
        ((Complex.arg d : Real.Angle) -
            (Complex.arg (-chord) : Real.Angle)).toReal) +
      (((Complex.arg chord : Real.Angle) -
            (Complex.arg c : Real.Angle)).toReal +
        ((Complex.arg b : Real.Angle) -
            (Complex.arg chord : Real.Angle)).toReal))


noncomputable def kwAntipodalEndpointTurnDefect
    (a b chord : ℂ) : ℝ :=
  ((Complex.arg b : Real.Angle) -
      (Complex.arg a : Real.Angle)).toReal -
    ((Complex.arg (-chord) : Real.Angle) -
      (Complex.arg a : Real.Angle)).toReal -
    ((Complex.arg b : Real.Angle) -
      (Complex.arg chord : Real.Angle)).toReal


end StatMech.FrontierA
