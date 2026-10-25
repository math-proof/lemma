/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

namespace FKIsingMedialDart

variable {P : PlanarZ2Subgraph}


def localMateEquiv (omega : ConfigSpace (Sym2 P.V)) :
    FKIsingMedialDart P ≃ FKIsingMedialDart P where
  toFun := localMate omega
  invFun := localMate omega
  left_inv := localMate_involutive omega
  right_inv := localMate_involutive omega


end FKIsingMedialDart
end
end StatMech.Universality
