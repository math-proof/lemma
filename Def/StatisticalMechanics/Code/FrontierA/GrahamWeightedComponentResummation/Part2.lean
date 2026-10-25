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
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponentResummation
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


def grahamAdmissibleComponentComplements (g k l : V) : Finset (Finset V) :=
  Finset.univ.filter (fun S => g ∉ S ∧ k ∈ S ∧ l ∈ S)


noncomputable def grahamDisconnectedPairMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (g k l : V) : Real :=
  ∑ S ∈ grahamAdmissibleComponentComplements g k l,
    grahamComponentPairMass G beta J S g {k, l}


noncomputable def grahamRestrictedVacuumComponentMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (g k l : V) : Real :=
  ∑ S ∈ grahamAdmissibleComponentComplements g k l,
    expectationJ G beta (StatMech.Sharpness.couplingIn J S) {k, l} *
      grahamComponentPairMass G beta J S g ∅


end StatMech.FrontierA
