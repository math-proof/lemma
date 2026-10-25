/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part3
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

namespace FKIsingDobrushinMedialComplex

variable {P : PlanarZ2Subgraph} (C : FKIsingDobrushinMedialComplex P)


def loopGraph (omega : ConfigSpace (Sym2 P.V)) :
    SimpleGraph (FKIsingMedialDart P) where
  Adj d e :=
    e = FKIsingMedialDart.localMate omega d ∨ e = C.bondMate d
  symm := by
    constructor
    intro d e h
    rcases h with rfl | rfl
    · left
      rw [FKIsingMedialDart.localMate_involutive]
    · right
      exact (C.bondMate_involutive d).symm
  loopless := ⟨by
    intro d h
    rcases h with h | h
    · exact FKIsingMedialDart.localMate_ne omega d h.symm
    · exact C.bondMate_ne d h.symm⟩

end FKIsingDobrushinMedialComplex
end
end StatMech.Universality
