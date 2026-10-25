/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterGhostLift.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostPinned
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W]
  [Fintype V] [DecidableEq V]


def lpTwoGhostBaseEdges (E : Finset (Sym2 W)) :
    Finset (Sym2 (LPTwoGhostVertex W)) :=
  E.image (Sym2.map Sum.inl)


def lpTwoGhostStarEdges (side : W -> Bool) :
    Finset (Sym2 (LPTwoGhostVertex W)) :=
  Finset.univ.image (fun x => s(Sum.inl x, Sum.inr (side x)))

def lpTwoGhostEdges (E : Finset (Sym2 W)) (side : W -> Bool) :
    Finset (Sym2 (LPTwoGhostVertex W)) :=
  lpTwoGhostBaseEdges E ∪ lpTwoGhostStarEdges side

end
end StatMech.Ising
