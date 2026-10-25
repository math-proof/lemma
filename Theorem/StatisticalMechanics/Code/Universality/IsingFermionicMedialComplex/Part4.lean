/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

namespace FKIsingDobrushinMedialComplex

variable {P : PlanarZ2Subgraph} (C : FKIsingDobrushinMedialComplex P)


theorem loopGraph_neighborFinset (omega : ConfigSpace (Sym2 P.V))
    (d : FKIsingMedialDart P) :
    (C.loopGraph omega).neighborFinset d =
      {FKIsingMedialDart.localMate omega d, C.bondMate d} := by
  ext e
  rw [SimpleGraph.mem_neighborFinset]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rfl

theorem loopGraph_degree_eq_two (omega : ConfigSpace (Sym2 P.V))
    (d : FKIsingMedialDart P) : (C.loopGraph omega).degree d = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    C.loopGraph_neighborFinset omega d]
  exact Finset.card_pair (C.bondMate_ne_localMate omega d).symm


end FKIsingDobrushinMedialComplex
end
end StatMech.Universality
