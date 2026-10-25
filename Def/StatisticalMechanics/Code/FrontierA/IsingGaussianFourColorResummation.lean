/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorFamilies.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourCurrentTree
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorEdgecopyBridge
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneResummation
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneCardBridge.Part2
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteTreeFourCurrentPatternSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (P : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) ->
      (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) -> Prop)
    (z : ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
      ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat))) : Real :=
  weight G beta J (ofEdgeFun G z.1.1) *
    weight G beta J (ofEdgeFun G z.1.2) *
    weight G beta J (ofEdgeFun G z.2.1) *
    weight G beta J (ofEdgeFun G z.2.2) *
    (if P z.1.1 z.1.2 z.2.1 z.2.2 then 1 else 0)


noncomputable def finiteTreeFourColorCoefficient
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat)
    (P : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) ->
      (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) -> Prop) : Real :=
  ∑ split : GrahamFourSplit G total,
    grahamFourSplitMultiplicity G total split *
      (if P split.1.1 split.1.2.1 split.1.2.2
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)
        then 1 else 0)


end StatMech.FrontierA
