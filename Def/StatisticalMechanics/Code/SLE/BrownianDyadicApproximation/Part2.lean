module
public import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicControl.Part3
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicApproximation
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.SLE

noncomputable def brownianDyadicLimit (N : Nat) (t : Real)
    (omega : Real -> Real) : Real :=
  limUnder atTop (fun n =>
    brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega)


end StatMech.SLE
