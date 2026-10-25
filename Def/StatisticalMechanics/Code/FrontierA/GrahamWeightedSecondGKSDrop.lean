/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSecondGKSDrop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFirstGKSDropGlobal.Part2
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamSecondComponentFiber
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (k : V)
    (A B : Finset V) (P : Current V -> Prop) [DecidablePred P] : Real :=
  gatedSourcePairSum G beta J A B
    (fun n => notConnComp G n k = S ∧ P n)


noncomputable def grahamSecondComponentContext
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (k l : V) : Real :=
  ∑' bd, claim1Context G beta J S
    (fun n => notConnComp G n k = S) {k, l} ∅ bd

end StatMech.FrontierA
