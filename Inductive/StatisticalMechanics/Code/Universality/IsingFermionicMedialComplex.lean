/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
public import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

public inductive FKIsingMedialSide
  | west | east | south | north
deriving DecidableEq, Fintype


end
end StatMech.Universality
