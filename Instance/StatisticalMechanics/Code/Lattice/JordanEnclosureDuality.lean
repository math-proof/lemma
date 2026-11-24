module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepReconnect.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanFiniteDetour.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingClose.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part2
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

noncomputable instance jed_primalGraph_locallyFinite (E : Set (Sym2 (Site 2))) :
    SimpleGraph.LocallyFinite (jed_primalGraph E) := fun _ =>
  Set.Finite.fintype (Set.Finite.subset (Set.toFinite _) (fun _ hw =>
    (SimpleGraph.mem_neighborSet _ _ _).mpr (jed_primalGraph_le E hw)))


end Lattice
end StatMech
