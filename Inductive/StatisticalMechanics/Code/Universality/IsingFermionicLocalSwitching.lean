/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part11
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

inductive PointwiseExplorationSwitchingCase
    (crossingEdge : Sym2 P.V) (edges : Fin 4 -> M)
    (omega : ConfigSpace (Sym2 P.V)) : Type
  | caseOne
      (closed_not_mem : forall k,
        edges k ∉ D.exploration (setClosed crossingEdge omega))
      (open_not_mem : forall k,
        edges k ∉ D.exploration (setOpen crossingEdge omega))
  | caseTwo
      (paired_balance :
        (D.fermionicSummand (setClosed crossingEdge omega) (edges 0) +
            D.fermionicSummand (setOpen crossingEdge omega) (edges 0)) -
          (D.fermionicSummand (setClosed crossingEdge omega) (edges 1) +
            D.fermionicSummand (setOpen crossingEdge omega) (edges 1)) =
        Complex.I *
          ((D.fermionicSummand (setClosed crossingEdge omega) (edges 2) +
              D.fermionicSummand (setOpen crossingEdge omega) (edges 2)) -
            (D.fermionicSummand (setClosed crossingEdge omega) (edges 3) +
              D.fermionicSummand (setOpen crossingEdge omega) (edges 3))))
  | caseThree
      (paired_balance :
        (D.fermionicSummand (setClosed crossingEdge omega) (edges 0) +
            D.fermionicSummand (setOpen crossingEdge omega) (edges 0)) -
          (D.fermionicSummand (setClosed crossingEdge omega) (edges 1) +
            D.fermionicSummand (setOpen crossingEdge omega) (edges 1)) =
        Complex.I *
          ((D.fermionicSummand (setClosed crossingEdge omega) (edges 2) +
              D.fermionicSummand (setOpen crossingEdge omega) (edges 2)) -
            (D.fermionicSummand (setClosed crossingEdge omega) (edges 3) +
              D.fermionicSummand (setOpen crossingEdge omega) (edges 3))))

end FKIsingDobrushinDomain
end
end StatMech.Universality
