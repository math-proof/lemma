module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
open MeasureTheory
open scoped ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MassTransport.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ} {E : Type*}


def IsDiagonallyInvariantTransport
    [MulAction (Multiplicative (Site d)) E]
    (F : Site d → Site d → ConfigSpace E → ENNReal) : Prop :=
  ∀ (g : Multiplicative (Site d)) (x y : Site d) (omega : ConfigSpace E),
    F (g • x) (g • y) (shift g omega) = F x y omega


end StatMech.FrontierA
