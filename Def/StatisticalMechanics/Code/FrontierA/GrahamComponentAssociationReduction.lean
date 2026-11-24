module
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneFiber
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedGateShift
public import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentAssociationReduction
open Finset SimpleGraph
open scoped BigOperators
open Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentAssociationReduction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamCutPairCorrelation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (x y : V) (S : Finset V) : Real :=
  if x ∈ S ∧ y ∈ S then expectationJ G beta (couplingIn J S) {x, y} else 0


end StatMech.FrontierA
