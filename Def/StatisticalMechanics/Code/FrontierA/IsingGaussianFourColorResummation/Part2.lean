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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorResummation
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]


def finiteTreeMixedCurrentPattern
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j k l : V)
    (a b c d : G.edgeFinset -> Nat) : Prop :=
  sources G (ofEdgeFun G a) = {i, j} ∧
    sources G (ofEdgeFun G b) = {k, l} ∧
    sources G (ofEdgeFun G c) = ∅ ∧
    sources G (ofEdgeFun G d) = ∅ ∧
    CurrentConnected G (ofEdgeFun G (fun e => a e + b e)) i k


def finiteTreeSeparatedCurrentPattern
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j k l y : V)
    (a b c d : G.edgeFinset -> Nat) : Prop :=
  sources G (ofEdgeFun G a) = {i, j} ∧
    sources G (ofEdgeFun G b) = ∅ ∧
    sources G (ofEdgeFun G c) = {k, l} ∧
    sources G (ofEdgeFun G d) = ∅ ∧
    CurrentConnected G (ofEdgeFun G (fun e => a e + b e)) i y ∧
    CurrentConnected G (ofEdgeFun G (fun e => c e + d e)) k y

end StatMech.FrontierA
