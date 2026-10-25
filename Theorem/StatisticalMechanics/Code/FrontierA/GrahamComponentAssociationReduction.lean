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
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem couplingIn_couplingIn_of_subset
    (J : Sym2 V -> Real) {S T : Finset V} (hST : S ⊆ T) :
    couplingIn (couplingIn J T) S = couplingIn J S := by
  funext e
  unfold couplingIn
  by_cases hS : edgeInside S e
  · have hT : edgeInside T e := by
      intro x hx
      exact hST (hS x hx)
    simp [hS, hT]
  · simp [hS]


end StatMech.FrontierA
