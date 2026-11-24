module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.ClusterRunsAxisFE.Part2
public import Theorem.StatisticalMechanics.Code.Walls.bc_cutmeetsaxis
public import Theorem.StatisticalMechanics.Code.Walls.bc_mouthcorridor
public import Theorem.StatisticalMechanics.Code.Walls.bc_raydisjoint
public import Theorem.StatisticalMechanics.Code.Walls.bc_forcemono
public import Theorem.StatisticalMechanics.Code.Walls.bc_core
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Percolation

variable {d : ℕ}


def bc_BoxNearAxis (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      ∃ j₁ j₂ j₃ : Fin d,
        bc_NearAxis ω x₁ j₁ ∧ bc_NearAxis ω x₂ j₂ ∧ bc_NearAxis ω x₃ j₃


end Walls
end StatMech
