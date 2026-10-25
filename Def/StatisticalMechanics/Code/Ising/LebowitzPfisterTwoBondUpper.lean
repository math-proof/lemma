/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBondUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBondUpper.Part2
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
open Set
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

open StatMech.Sharpness


def twoBondInterfaceFreeEnergy (K m1 m2 c : Real) : Real :=
  let t := Real.tanh K
  Real.log ((1 + t * (m1 ^ 2 + m2 ^ 2) + t ^ 2 * c ^ 2) /
    (1 - t * (m1 ^ 2 + m2 ^ 2) + t ^ 2 * c ^ 2))


end
end StatMech.Ising
