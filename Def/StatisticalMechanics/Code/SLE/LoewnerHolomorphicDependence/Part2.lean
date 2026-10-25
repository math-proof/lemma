/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part15
import Mathlib.Analysis.Complex.Conformal
import Theorem.StatisticalMechanics.Code.SLE.LoewnerHolomorphicDependence.Part2
open Complex Set Metric Filter Topology
open scoped Interval


namespace StatMech.SLE

noncomputable section

def HasLoewnerLocalInitialVariationalFormula (W : Real -> Real) : Prop :=
  forall (s u : Real) (z : Complex), 0 <= u -> z ∈ upperHalfPlane ->
    u < z.im ^ 2 / 16 ->
    HasDerivAt (loewnerMaximalMaps (fun r => W (s + r)) u)
      (loewnerInitialJacobian (fun r => W (s + r)) u z) z


end
end StatMech.SLE
