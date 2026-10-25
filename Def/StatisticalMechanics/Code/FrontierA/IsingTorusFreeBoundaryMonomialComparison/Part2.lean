/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusPlusBoundaryField.Part2
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryMonomial
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryMonomialComparison
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteCutConditionalSpinProdNumerator (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (A : Finset {v : V // v ∈ S}) : Real :=
  ∑ inside : ConfigSpace {v : V // v ∈ S},
    spinProd A inside *
      wJ (finiteCutGraph G S).edgeFinset (fun _ ↦ beta)
        (fun z ↦ beta * finiteCutBoundaryField G S outside z) inside

end
end StatMech.FrontierA
