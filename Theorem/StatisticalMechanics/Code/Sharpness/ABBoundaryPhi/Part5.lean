module
public import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryProfile.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part13
public import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
public import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
public import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
public import Mathlib.Data.Finset.Preimage
public import Def.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part4
open Filter Finset Set SimpleGraph Topology
open scoped NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation


theorem abbSurfaceValue_spec {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) (z : S) :
    (z : Option (sctBox d n)) = some (abbSurfaceValue hocc z) :=
  Classical.choose_spec (abb_surface_eq_some_of_occurs hocc z.property)


end Sharpness
end StatMech
