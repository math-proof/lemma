module
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityApproximation.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityDiagonal
open Filter MeasureTheory Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityDiagonal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Lattice

variable {d : ℕ}


def CurrentPairConnectivityNoEscape
    (mu nu : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (x y : Site d) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ M : ℕ, ∀ m, M ≤ m →
    ∀ᶠ k in atTop,
      ((mu k).prod (nu k) : Measure _).real
        (currentPairTraceBoxGate Q k x y \
          currentPairTraceBoxGate Q m x y) < epsilon


end StatMech.FrontierB
