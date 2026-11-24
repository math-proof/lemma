module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.PeierlsClose.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection
open Set Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.Ising

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def regionDel (d : ℕ) (F : Set (Sym2 (Site d))) : Set (Site d) :=
  {x | ((hypercubicLattice d).deleteEdges F).Reachable (origin d) x}


end Lattice
end StatMech
