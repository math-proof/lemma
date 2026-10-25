/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFirstGKSDropGlobal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFirstGKSDrop
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFirstGKSDropGlobal
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


def grahamFirstAdmissibleComponentComplements
    (i j k l m : V) : Finset (Finset V) :=
  Finset.univ.filter (fun S =>
    i ∉ S ∧ j ∉ S ∧ k ∈ S ∧ l ∈ S ∧ m ∈ S)


noncomputable def grahamFirstRemainderMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l m : V) : Real :=
  gatedSourcePairSum G beta J {i, j} ∅
    (fun n => ¬ CurrentConnected G n i m ∧
      ¬ CurrentConnected G n i k ∧ ¬ CurrentConnected G n i l)


noncomputable def grahamFirstMixedRemainderMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l m : V) : Real :=
  gatedSourcePairSum G beta J {i, j} {k, l}
    (fun n => ¬ CurrentConnected G n i m ∧
      ¬ CurrentConnected G n i k)


end StatMech.FrontierA
