/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutPairAssociation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentAssociationReduction.Part3
import Mathlib.Combinatorics.SetFamily.FourFunctions
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


def GrahamCutPairAssociationAt
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) : Prop :=
  (∑ S : Finset V, isingCutMass G beta J m S *
      grahamCutPairCorrelation G beta J j k S) *
      (∑ S : Finset V, isingCutMass G beta J m S *
        grahamCutPairCorrelation G beta J k l S) <=
    ∑ S : Finset V, isingCutMass G beta J m S *
      (grahamCutPairCorrelation G beta J j k S *
        grahamCutPairCorrelation G beta J k l S)


end StatMech.FrontierA
