/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianKolmogorovTail
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicControl.Part2
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech.SLE

def brownianDyadicBadEvent (N n : Nat) : Set (Real -> Real) :=
  ⋃ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
    brownianDyadicEdgeBadEvent N n k


end StatMech.SLE
