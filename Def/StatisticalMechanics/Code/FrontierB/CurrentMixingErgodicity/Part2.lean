module
public import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity
open MeasureTheory Set
open scoped ENNReal symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentMixingErgodicity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

variable {E H : Type*} [Group H] [MulAction H E]


def CurrentCylinderPairMixing [Countable E]
    (mu : Measure (InfiniteCurrentConfig E)) : Prop :=
  ∀ (family : Finset (Set (InfiniteCurrentConfig E))),
    (∀ A ∈ family, A ∈ measurableCylinders (fun _ : E => Nat)) ->
    ∀ epsilon : Real, 0 < epsilon ->
      ∃ g : H, ∀ A ∈ family, ∀ B ∈ family,
        abs (mu.real (A ∩ (currentShift g) ⁻¹' B) -
          mu.real A * mu.real B) < epsilon


end StatMech.FrontierB
