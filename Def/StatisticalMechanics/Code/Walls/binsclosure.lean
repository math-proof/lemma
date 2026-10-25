/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.binsinsertion.Part7
import Structure.StatisticalMechanics.Code.Walls.binsclosure
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 20000


def bins_branchEdges (B : Fin 3 → bins_Branch) : Finset (Sym2 (Site 2)) :=
  (Finset.univ.biUnion fun i => (B i).P.edges.toFinset) ∪
    Finset.univ.image (fun i => s((B i).v, (B i).u))


def bins_branchSide (rho : ConfigSpace (Sym2 (Site 2))) (B : bins_Branch) : Set (Site 2) :=
  ({z | z ∈ B.P.support ∧ z ≠ ![0, 0]} : Set (Site 2)) ∪ cluster 2 rho B.u


end StatMech.Walls
