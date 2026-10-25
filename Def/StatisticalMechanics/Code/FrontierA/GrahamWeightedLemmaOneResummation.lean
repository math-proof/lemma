/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneFourColor
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourReplicaCore
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourCurrent
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option maxHeartbeats 8000000


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamLemmaOneMixedFourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) : Real :=
  ∑' z : ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
      ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)),
    ((if sources G (ofEdgeFun G z.1.1) = {j, k}
        then weight G beta J (ofEdgeFun G z.1.1) else 0) *
      (if sources G (ofEdgeFun G z.1.2) = {k, l}
        then weight G beta J (ofEdgeFun G z.1.2) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) k m
        then 1 else 0)) *
    ((if sources G (ofEdgeFun G z.2.1) = ∅
        then weight G beta J (ofEdgeFun G z.2.1) else 0) *
      (if sources G (ofEdgeFun G z.2.2) = ∅
        then weight G beta J (ofEdgeFun G z.2.2) else 0))


noncomputable def grahamLemmaOneSeparatedFourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) : Real :=
  ∑' z : ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
      ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)),
    ((if sources G (ofEdgeFun G z.1.1) = {j, k}
        then weight G beta J (ofEdgeFun G z.1.1) else 0) *
      (if sources G (ofEdgeFun G z.1.2) = ∅
        then weight G beta J (ofEdgeFun G z.1.2) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) k m
        then 1 else 0)) *
    ((if sources G (ofEdgeFun G z.2.1) = {k, l}
        then weight G beta J (ofEdgeFun G z.2.1) else 0) *
      (if sources G (ofEdgeFun G z.2.2) = ∅
        then weight G beta J (ofEdgeFun G z.2.2) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k m
        then 1 else 0))


def grahamFourthProfile
    {E : Type*} (total a b c : E -> Nat) : E -> Nat :=
  fun e => total e - a e - b e - c e


noncomputable def grahamFourSplitMultiplicity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat)
    (split : {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
        (G.edgeFinset -> Nat) //
      ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e}) : Real :=
  ∏ e : G.edgeFinset,
    (Nat.choose (total e) (split.1.1 e) : Real) *
      (Nat.choose (total e - split.1.1 e) (split.1.2.1 e) : Real) *
      (Nat.choose (total e - split.1.1 e - split.1.2.1 e)
        (split.1.2.2 e) : Real)


noncomputable def grahamLemmaOneMixedProfileCoefficient
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (j k l m : V) : Real :=
  ∑ split : {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
      (G.edgeFinset -> Nat) //
    ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e},
    grahamFourSplitMultiplicity G total split *
      (if sources G (ofEdgeFun G split.1.1) = {j, k} then 1 else 0) *
      (if sources G (ofEdgeFun G split.1.2.1) = {k, l} then 1 else 0) *
      (if sources G (ofEdgeFun G split.1.2.2) = ∅ then 1 else 0) *
      (if sources G (ofEdgeFun G
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) = ∅
        then 1 else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => split.1.1 e + split.1.2.1 e)) k m
        then 1 else 0)


noncomputable def grahamLemmaOneSeparatedProfileCoefficient
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (j k l m : V) : Real :=
  ∑ split : {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
      (G.edgeFinset -> Nat) //
    ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e},
    grahamFourSplitMultiplicity G total split *
      (if sources G (ofEdgeFun G split.1.1) = {j, k} then 1 else 0) *
      (if sources G (ofEdgeFun G split.1.2.1) = ∅ then 1 else 0) *
      (if sources G (ofEdgeFun G split.1.2.2) = {k, l} then 1 else 0) *
      (if sources G (ofEdgeFun G
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) = ∅
        then 1 else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => split.1.1 e + split.1.2.1 e)) k m
        then 1 else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => split.1.2.2 e +
            grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2 e)) k m
        then 1 else 0)


noncomputable def grahamLemmaOneMixedProfileMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) : Real :=
  ∑' total : G.edgeFinset -> Nat,
    ∑ split : {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
        (G.edgeFinset -> Nat) //
      ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e},
      (if sources G (ofEdgeFun G split.1.1) = {j, k}
        then weight G beta J (ofEdgeFun G split.1.1) else 0) *
      (if sources G (ofEdgeFun G split.1.2.1) = {k, l}
        then weight G beta J (ofEdgeFun G split.1.2.1) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => split.1.1 e + split.1.2.1 e)) k m
        then 1 else 0) *
      (if sources G (ofEdgeFun G split.1.2.2) = ∅
        then weight G beta J (ofEdgeFun G split.1.2.2) else 0) *
      (if sources G (ofEdgeFun G
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) = ∅
        then weight G beta J (ofEdgeFun G
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) else 0)


noncomputable def grahamLemmaOneSeparatedProfileMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) : Real :=
  ∑' total : G.edgeFinset -> Nat,
    ∑ split : {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
        (G.edgeFinset -> Nat) //
      ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e},
      (if sources G (ofEdgeFun G split.1.1) = {j, k}
        then weight G beta J (ofEdgeFun G split.1.1) else 0) *
      (if sources G (ofEdgeFun G split.1.2.1) = ∅
        then weight G beta J (ofEdgeFun G split.1.2.1) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => split.1.1 e + split.1.2.1 e)) k m
        then 1 else 0) *
      (if sources G (ofEdgeFun G split.1.2.2) = {k, l}
        then weight G beta J (ofEdgeFun G split.1.2.2) else 0) *
      (if sources G (ofEdgeFun G
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) = ∅
        then weight G beta J (ofEdgeFun G
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => split.1.2.2 e +
            grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2 e)) k m
        then 1 else 0)


end StatMech.FrontierA
