/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentChainClosure
open Filter MeasureTheory Set Topology
open scoped symmDiff


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation Sharpness

open StatMech.OSSS.FKSharpnessWeightedPhaseTransport

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


def fmu_AxisCofinalPairMixing (axis : Nat → H)
    (rho : Measure (ConfigSpace E)) : Prop :=
  ∀ (P : Finset (Finset E)), ∀ epsilon : Real, 0 < epsilon → ∀ K : Nat,
    ∃ k : Nat, K ≤ k ∧ ∀ T ∈ P, ∀ U ∈ P,
      abs (rho.real (fmu_multiOpen T ∩
          (shift (axis k)) ⁻¹' fmu_multiOpen U) -
        rho.real (fmu_multiOpen T) * rho.real (fmu_multiOpen U)) < epsilon


end StatMech.FrontierB
