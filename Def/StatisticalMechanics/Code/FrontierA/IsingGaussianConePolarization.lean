/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Mathlib.LinearAlgebra.Lagrange
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization
open Filter Finset Polynomial Topology


namespace StatMech.FrontierA

def smearingPositivePart {V : Type*} (a : V -> Real) : V -> Real :=
  fun v => max (a v) 0


def smearingNegativePart {V : Type*} (a : V -> Real) : V -> Real :=
  fun v => max (-a v) 0

end StatMech.FrontierA
