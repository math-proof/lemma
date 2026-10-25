/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexProjPhaseClose.Part2


namespace StatMech.Universality

open Complex

open scoped Real BigOperators


noncomputable def hpp_witness : hpp_BoundaryIntegralData where
  A := 0
  B := 1
  E := 0
  Fa := 1
  alphaFSum := ((1 - hexBdryCl * 0 : ℝ) : ℂ)
  alphaFSum_eq := by norm_num
  betaFSum := ((1 : ℝ) : ℂ)
  betaFSum_eq := rfl
  epsFSum := Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) * (((0:ℝ)/2 : ℝ) : ℂ)
  epsFSum_eq := rfl
  epsbarFSum := Complex.exp ((hbi_sigma * (2*Real.pi/3) : ℝ) * Complex.I) * (((0:ℝ)/2 : ℝ) : ℂ)
  epsbarFSum_eq := rfl


end StatMech.Universality
