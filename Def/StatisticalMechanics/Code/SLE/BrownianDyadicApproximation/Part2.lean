/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicControl.Part3
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicApproximation
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech.SLE

noncomputable def brownianDyadicLimit (N : Nat) (t : Real)
    (omega : Real -> Real) : Real :=
  limUnder atTop (fun n =>
    brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega)


end StatMech.SLE
