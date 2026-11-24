module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part2
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


open Classical in


noncomputable def leftExitIndex (hfin : (cluster 2 ω (origin 2)).Finite) : ℕ := by
  classical
  exact Nat.find (leftExitPred_exists (ω := ω) hfin)


end Lattice
end StatMech
