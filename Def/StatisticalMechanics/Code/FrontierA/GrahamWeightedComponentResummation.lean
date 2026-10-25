/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponent.Part2
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part4
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamComponentPairMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (g : V)
    (A : Finset V) : Real :=
  ∑' pq : (↥G.edgeFinset -> Nat) × (↥G.edgeFinset -> Nat),
    (if sources G (ofEdgeFun G pq.1) = A
      then weight G beta J (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = ∅
      then weight G beta J (ofEdgeFun G pq.2) else 0) *
    (if notConnComp G
        (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
      then 1 else 0)


end StatMech.FrontierA
