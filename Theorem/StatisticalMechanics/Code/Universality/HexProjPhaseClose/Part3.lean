/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexProjPhaseClose


namespace StatMech.Universality

open Complex

open scoped Real BigOperators


theorem hpp_witness_vanish :
    (1/2 : ℂ) * hexUnit 4 * hpp_witness.alphaFSum
      + (1/2 : ℂ) * hexUnit 1 * hpp_witness.betaFSum
      + ((1/2 : ℂ) * hexUnit 3 * hpp_witness.epsFSum
          + (1/2 : ℂ) * hexUnit (-1) * hpp_witness.epsbarFSum) = 0 := by
  change (1 / 2 : ℂ) * hexUnit 4 * (((1 - hexBdryCl * 0 : ℝ) : ℂ))
      + (1 / 2 : ℂ) * hexUnit 1 * (((1 : ℝ) : ℂ))
      + ((1 / 2 : ℂ) * hexUnit 3
            * (Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I) * (((0:ℝ) / 2 : ℝ) : ℂ))
          + (1 / 2 : ℂ) * hexUnit (-1)
            * (Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I) * (((0:ℝ) / 2 : ℝ) : ℂ))) = 0
  rw [hpp_alphaDir, hpp_topDir]
  simp only [mul_zero, zero_div, Complex.ofReal_zero, mul_zero, add_zero]
  push_cast; ring


theorem hpp_witness_identity :
    hexBdryCl * hpp_witness.A + hexBdryCt * hpp_witness.E + hpp_witness.B = 1 :=
  hpp_witness.boundaryIdentity rfl hpp_witness_vanish

end StatMech.Universality
