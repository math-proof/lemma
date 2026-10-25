/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part4
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

namespace FKIsingDobrushinMedialComplex

variable {P : PlanarZ2Subgraph} (C : FKIsingDobrushinMedialComplex P)


def explorationFinset (omega : ConfigSpace (Sym2 P.V)) :
    Finset (FKIsingMedialDart P) :=
  Finset.univ.filter fun d => (C.loopGraph omega).Reachable C.sourceDart d

def exploration (omega : ConfigSpace (Sym2 P.V)) :
    List (FKIsingMedialDart P) :=
  (C.explorationFinset omega).toList

end FKIsingDobrushinMedialComplex
end
end StatMech.Universality
