/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

namespace FKIsingMedialDart

variable {P : PlanarZ2Subgraph}


def localMate (omega : ConfigSpace (Sym2 P.V))
    (d : FKIsingMedialDart P) : FKIsingMedialDart P :=
  match omega d.1.1, d.2 with
  | false, .west => (d.1, .south)
  | false, .south => (d.1, .west)
  | false, .east => (d.1, .north)
  | false, .north => (d.1, .east)
  | true, .west => (d.1, .north)
  | true, .north => (d.1, .west)
  | true, .east => (d.1, .south)
  | true, .south => (d.1, .east)

end FKIsingMedialDart
end
end StatMech.Universality
