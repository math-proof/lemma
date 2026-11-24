module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
public import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part2
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

noncomputable def wcl_chosenWalk (o f : Site 2) : (hypercubicLattice 2).Walk o f :=
  (pbs_reach_all o f).some


noncomputable def wcl_windingColoring (flip : Site 2 → Site 2 → Prop) (o : Site 2) :
    Site 2 → Prop :=
  fun f => Odd (wcl_flipCount flip (wcl_chosenWalk o f))


end Lattice
end StatMech
