/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeCurrentAfterMixing
import Theorem.StatisticalMechanics.Code.FrontierB.PlusAxisMixing
import Theorem.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceCoarseUniqueness
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityPersistence
import Theorem.StatisticalMechanics.Code.FK.PairMixingGenMixing
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


def fmu_AxisEventuallyGenMixing (axis : Nat -> H)
    (rho : Measure (ConfigSpace E)) : Prop :=
  ∀ (family : Finset (Set (ConfigSpace E))),
    (∀ A ∈ family,
      A ∈ measurableCylinders (fun _ : E => Bool)) ->
    ∀ epsilon : Real, 0 < epsilon ->
      ∀ᶠ k : Nat in atTop, ∀ A ∈ family, ∀ B ∈ family,
        abs (rho.real (A ∩ (shift (axis k)) ⁻¹' B) -
          rho.real A * rho.real B) < epsilon


def fmu_AxisCofinalGenMixing (axis : Nat -> H)
    (rho : Measure (ConfigSpace E)) : Prop :=
  ∀ (family : Finset (Set (ConfigSpace E))),
    (∀ A ∈ family,
      A ∈ measurableCylinders (fun _ : E => Bool)) ->
    ∀ epsilon : Real, 0 < epsilon -> ∀ K : Nat,
      ∃ k : Nat, K <= k ∧ ∀ A ∈ family, ∀ B ∈ family,
        abs (rho.real (A ∩ (shift (axis k)) ⁻¹' B) -
          rho.real A * rho.real B) < epsilon


end StatMech.FrontierB
