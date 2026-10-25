/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSecondGKSDropGlobal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedSecondGKSDrop
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


def grahamSecondAdmissibleComponentComplements
    (i j k l m : V) : Finset (Finset V) :=
  Finset.univ.filter (fun S =>
    i ∈ S ∧ j ∈ S ∧ m ∈ S ∧ k ∉ S ∧ l ∉ S)

noncomputable def grahamSecondRemainderMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l m : V) : Real :=
  gatedSourcePairSum G beta J {k, l} ∅
    (fun n => ¬ CurrentConnected G n k m ∧
      ¬ CurrentConnected G n k i ∧ ¬ CurrentConnected G n k j)

noncomputable def grahamSecondMixedRemainderMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l m : V) : Real :=
  gatedSourcePairSum G beta J {i, j} {k, l}
    (fun n => ¬ CurrentConnected G n i k ∧ CurrentConnected G n i m)

end StatMech.FrontierA
