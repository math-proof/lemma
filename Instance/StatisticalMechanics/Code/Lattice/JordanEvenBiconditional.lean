module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

noncomputable instance jeb_imageGraph_locallyFinite (P : PlanarZ2Subgraph) :
    SimpleGraph.LocallyFinite (imageGraph P) := fun v =>
  Set.Finite.fintype (Set.Finite.subset (Set.toFinite _) (fun w hw =>
    (SimpleGraph.mem_neighborSet _ _ _).mpr (imageGraph_le_lattice P hw)))


end Lattice
end StatMech
