/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteSpectralBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSymbolReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteSpectralBridge
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def quantumIsingNormalizedSpinSector
    (beta h : Real) (L : Nat) [Fact (2 < L)] (a b : Fin 2) : Complex :=
  ((2 * Real.exp (-quantumIsingVerticalCoupling beta h L) *
      (Real.cosh (beta / (4 * L)) *
        Real.cosh (quantumIsingVerticalCoupling beta h L))) ^ (L * L) : Real) *
    ons_weightedSpinCharacterSum L
      (anisotropicSquareEdgeWeight L
        (Real.tanh (beta / (4 * L)))
        (Real.tanh (quantumIsingVerticalCoupling beta h L))) a b


end StatMech.FrontierA
