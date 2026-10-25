/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConnFinal
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose


namespace StatMech.Universality

open Complex Filter Topology

open scoped Real BigOperators Topology


structure HexFObsBoundaryData where
  
  lam : ℝ
  
  ups : ℝ
  
  tau : ℝ
  
  Fa : ℝ
  


  alphaRest : ℂ
  
  alphaRest_eq : alphaRest
    = (Complex.exp ((-(hbi_sigma * Real.pi) : ℝ) * Complex.I)
        + Complex.exp ((hbi_sigma * Real.pi : ℝ) * Complex.I)) / 2 * (lam : ℂ)
  
  betaSum : ℂ
  
  betaSum_eq : betaSum = (ups : ℂ)
  

  epsSum : ℂ
  
  epsSum_eq : epsSum
    = Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I) * ((tau / 2 : ℝ) : ℂ)
  

  epsbarSum : ℂ
  
  epsbarSum_eq : epsbarSum
    = Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I) * ((tau / 2 : ℝ) : ℂ)
  


  raw : -((Fa : ℂ) + alphaRest) + betaSum
      + hbi_j * epsSum + (starRingEnd ℂ) hbi_j * epsbarSum = 0

end StatMech.Universality
