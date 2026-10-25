/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourCurrentTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFiniteCurrentUrsell.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedAuxiliaryAlgebra
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteTreeMixedFourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑' z : ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
      ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)),
    ((if sources G (ofEdgeFun G z.1.1) = grahamPairSupport i j
        then weight G beta J (ofEdgeFun G z.1.1) else 0) *
      (if sources G (ofEdgeFun G z.1.2) = grahamPairSupport k l
        then weight G beta J (ofEdgeFun G z.1.2) else 0) *
      (if CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i k
        then 1 else 0)) *
    ((if sources G (ofEdgeFun G z.2.1) = ∅
        then weight G beta J (ofEdgeFun G z.2.1) else 0) *
      (if sources G (ofEdgeFun G z.2.2) = ∅
        then weight G beta J (ofEdgeFun G z.2.2) else 0))


noncomputable def finiteTreeSeparatedFourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l y : V) : Real :=
  ∑' z : ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
      ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)),
    ((if sources G (ofEdgeFun G z.1.1) = grahamPairSupport i j
        then weight G beta J (ofEdgeFun G z.1.1) else 0) *
      (if sources G (ofEdgeFun G z.1.2) = ∅
        then weight G beta J (ofEdgeFun G z.1.2) else 0) *
      (if CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y
        then 1 else 0)) *
    ((if sources G (ofEdgeFun G z.2.1) = grahamPairSupport k l
        then weight G beta J (ofEdgeFun G z.2.1) else 0) *
      (if sources G (ofEdgeFun G z.2.2) = ∅
        then weight G beta J (ofEdgeFun G z.2.2) else 0) *
      (if CurrentConnected G
          (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
        then 1 else 0))


end StatMech.FrontierA
