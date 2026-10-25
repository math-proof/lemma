/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneCardBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorEdgecopyBridge
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneResummation
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneCardBridge
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def grahamMixedProfileIndicator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total a b c : G.edgeFinset -> Nat) (j k l m : V) : Real :=
  (if sources G (ofEdgeFun G a) = {j, k} then 1 else 0) *
    (if sources G (ofEdgeFun G b) = {k, l} then 1 else 0) *
    (if sources G (ofEdgeFun G c) = ∅ then 1 else 0) *
    (if sources G (ofEdgeFun G (grahamFourthProfile total a b c)) = ∅
      then 1 else 0) *
    (if ¬ CurrentConnected G (ofEdgeFun G (fun e => a e + b e)) k m
      then 1 else 0)


noncomputable def grahamSeparatedProfileIndicator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total a b c : G.edgeFinset -> Nat) (j k l m : V) : Real :=
  (if sources G (ofEdgeFun G a) = {j, k} then 1 else 0) *
    (if sources G (ofEdgeFun G b) = ∅ then 1 else 0) *
    (if sources G (ofEdgeFun G c) = {k, l} then 1 else 0) *
    (if sources G (ofEdgeFun G (grahamFourthProfile total a b c)) = ∅
      then 1 else 0) *
    (if ¬ CurrentConnected G (ofEdgeFun G (fun e => a e + b e)) k m
      then 1 else 0) *
    (if ¬ CurrentConnected G
        (ofEdgeFun G (fun e => c e + grahamFourthProfile total a b c e)) k m
      then 1 else 0)

end StatMech.FrontierA
