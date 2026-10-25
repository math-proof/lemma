/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianKolmogorovTail
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicControl
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech.SLE

def brownianDyadicEdgeBadEvent (N n k : Nat) : Set (Real -> Real) :=
  {omega | brownianDyadicThreshold n <=
    edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
      (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega)}


end StatMech.SLE
