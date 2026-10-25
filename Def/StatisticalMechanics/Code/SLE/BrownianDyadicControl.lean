/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianKolmogorovTail
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech.SLE

def brownianDyadicDenominator (n : Nat) : Nat := 256 ^ n


noncomputable def brownianDyadicPoint (N n k : Nat) : Real :=
  -(N : Real) + (k : Real) / brownianDyadicDenominator n


noncomputable def brownianDyadicThreshold (n : Nat) : ENNReal :=
  (2 : ENNReal)⁻¹ ^ n

end StatMech.SLE
