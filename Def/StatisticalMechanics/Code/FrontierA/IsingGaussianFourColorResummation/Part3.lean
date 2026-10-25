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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorResummation.Part2
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]


def FiniteTreeColoringCardBound
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j k l : V) : Prop :=
  ∀ total : G.edgeFinset -> Nat,
    #(finiteTreeMixedColorings (endsM G total)
        Finset.univ i j k l) <=
      ∑ y : V, #(finiteTreeSeparatedBranchColorings (endsM G total)
        Finset.univ i j k l y)


end StatMech.FrontierA
