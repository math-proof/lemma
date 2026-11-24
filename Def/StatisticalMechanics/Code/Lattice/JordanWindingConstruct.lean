module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepDual.Part4
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

noncomputable def jwn_cutCount (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ :=
  wcl_flipCount (wcl_cutFlip H f0 g0) w


end Lattice
end StatMech
