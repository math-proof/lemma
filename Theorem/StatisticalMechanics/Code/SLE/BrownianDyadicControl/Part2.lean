/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianKolmogorovTail
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Def.StatisticalMechanics.Code.SLE.BrownianDyadicControl.Part2
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech.SLE

theorem brownianProductLaw_brownianDyadicEdgeBadEvent_le (N n k : Nat) :
    brownianProductLaw (brownianDyadicEdgeBadEvent N n k) <=
      ((3 : NNReal) *
        (((brownianDyadicDenominator n : Nat) : ENNReal)⁻¹) ^ (2 : Real)) /
        (brownianDyadicThreshold n) ^ (4 : Nat) := by
  have h := brownianCoordinateProcess_measure_edist_ge_le
    (brownianDyadicPoint N n k) (brownianDyadicPoint N n (k + 1))
    (brownianDyadicThreshold n)
    (by simp [brownianDyadicThreshold])
    (by simp [brownianDyadicThreshold])
  rw [edist_brownianDyadicPoint_succ] at h
  exact h


end StatMech.SLE
