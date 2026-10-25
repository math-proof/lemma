/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedBridgeGap
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part4
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option maxHeartbeats 8000000


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def grahamSourcePairComponentFiber
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (m : V)
    (A B : Finset V) : Real :=
  gatedSourcePairSum G beta J A B
    (fun n => notConnComp G n m = S)

noncomputable def grahamComponentExteriorContext
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (m : V) : Real :=
  ∑' bd, claim1Context G beta J S
    (fun n => notConnComp G n m = S) ∅ ∅ bd

end StatMech.FrontierA
