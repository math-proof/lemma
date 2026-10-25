/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPTransfer
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


structure CrossingTransportData
    (μsq μtri : Measure (ConfigSpace (Sym2 (Site 2))))
    (ρsq ρtri : ℝ) : Prop where
  
  one_lt_ρsq : 1 < ρsq
  
  one_lt_ρtri : 1 < ρtri
  


  sqDominatedByTri : ∀ n0 : ℕ, ∀ x ∈ boxCrossingProbabilities μsq ρsq n0,
      ∃ y ∈ boxCrossingProbabilities μtri ρtri n0, y ≤ x
  


  triDominatedBySq : ∀ n0 : ℕ, ∀ x ∈ boxCrossingProbabilities μtri ρtri n0,
      ∃ y ∈ boxCrossingProbabilities μsq ρsq n0, y ≤ x


end Universality
end StatMech
