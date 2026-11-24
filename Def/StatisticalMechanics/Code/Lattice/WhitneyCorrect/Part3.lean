module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part3
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def whc_CutColoring (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) (φ : Site 2 → Prop) : Prop :=
  ∀ a b, (hypercubicLattice 2).Adj a b →
    ((whc_isCross H a b ∨ s(a, b) = s(f0, g0)) ↔ (φ a ↔ ¬ φ b))


end Lattice
end StatMech
