/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part15
import Mathlib.Analysis.Complex.Conformal
import Theorem.StatisticalMechanics.Code.SLE.LoewnerHolomorphicDependence
open Complex Set Metric Filter Topology
open scoped Interval


namespace StatMech.SLE

noncomputable section

def loewnerInitialVariationalCoefficient
    (W : Real -> Real) (z : Complex) (s : Real) : Complex :=
  -2 / (loewnerMaximalMaps W s z - (W s : Complex)) ^ 2


def loewnerInitialJacobian
    (W : Real -> Real) (t : Real) (z : Complex) : Complex :=
  Complex.exp
    (∫ s in (0 : Real)..t, loewnerInitialVariationalCoefficient W z s)


end
end StatMech.SLE
