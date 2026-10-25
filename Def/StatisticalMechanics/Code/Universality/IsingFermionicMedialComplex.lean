/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
import Inductive.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

def FKIsingMedialSide.angle : FKIsingMedialSide -> Real
  | .west => 0
  | .east => Real.pi
  | .south => -(Real.pi / 2)
  | .north => Real.pi / 2


end
end StatMech.Universality
