/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexProjPhaseClose


namespace StatMech.Universality

open Complex

open scoped Real BigOperators


structure hpp_BoundaryIntegralData where
  
  A : ℝ
  
  B : ℝ
  
  E : ℝ
  
  Fa : ℝ
  
  alphaFSum : ℂ
  
  alphaFSum_eq : alphaFSum = ((Fa - hexBdryCl * A : ℝ) : ℂ)
  
  betaFSum : ℂ
  
  betaFSum_eq : betaFSum = ((B : ℝ) : ℂ)
  
  epsFSum : ℂ
  
  epsFSum_eq : epsFSum
    = Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) * ((E/2 : ℝ) : ℂ)
  
  epsbarFSum : ℂ
  
  epsbarFSum_eq : epsbarFSum
    = Complex.exp ((hbi_sigma * (2*Real.pi/3) : ℝ) * Complex.I) * ((E/2 : ℝ) : ℂ)

end StatMech.Universality
