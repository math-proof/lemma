/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentAssociationReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneFiber
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedGateShift
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentAssociationReduction.Part2
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


def GrahamCutPositiveAssociation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (m : V) : Prop :=
  ∀ f g : Finset V -> Real, Monotone f -> Monotone g ->
    (∑ S : Finset V, isingCutMass G beta J m S * f S) *
        (∑ S : Finset V, isingCutMass G beta J m S * g S) ≤
      ∑ S : Finset V, isingCutMass G beta J m S * (f S * g S)


end StatMech.FrontierA
