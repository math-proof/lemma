/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConnFinal
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part2


namespace StatMech.Universality

open Complex Filter Topology

open scoped Real BigOperators Topology


noncomputable def hbi_witness : HexFObsBoundaryData where
  lam := 0
  ups := 1
  tau := 0
  Fa := 1
  alphaRest := (Complex.exp ((-(hbi_sigma * Real.pi) : ℝ) * Complex.I)
      + Complex.exp ((hbi_sigma * Real.pi : ℝ) * Complex.I)) / 2 * ((0 : ℝ) : ℂ)
  alphaRest_eq := rfl
  betaSum := ((1 : ℝ) : ℂ)
  betaSum_eq := rfl
  epsSum := Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I)
      * (((0 : ℝ) / 2 : ℝ) : ℂ)
  epsSum_eq := rfl
  epsbarSum := Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I)
      * (((0 : ℝ) / 2 : ℝ) : ℂ)
  epsbarSum_eq := rfl
  raw := by push_cast; ring


end StatMech.Universality
