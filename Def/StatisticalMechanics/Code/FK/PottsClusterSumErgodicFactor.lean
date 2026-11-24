module
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part10
open MeasureTheory Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumErgodicFactor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK

def IsErgodicFor {G Omega : Type*} [MeasurableSpace Omega]
    (shift : G -> Omega -> Omega) (mu : Measure Omega) : Prop :=
  (∀ g, MeasurePreserving (shift g) mu mu) ∧
    ∀ s : Set Omega, MeasurableSet s ->
      (∀ g, shift g ⁻¹' s = s) ->
        mu s = 0 ∨ mu s = mu Set.univ


end StatMech.FK
