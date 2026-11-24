module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Walls.welenterleave.Part2
public import Def.StatisticalMechanics.Code.Walls.wdjdufourdjct.Part4
open Finset Set SimpleGraph
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.Walls


attribute [instance] wdj_Hypermap.finD wdj_Hypermap.decD

theorem wdj_JordanIncrement_witness :
    wdj_JordanIncrement ⟨15, 7, 6, 6, 3⟩ ⟨15, 7, 7, 5, 4⟩ := by
  unfold wdj_JordanIncrement; decide


theorem wdj_JordanIncrement_iff_nc (before after : wdj_HypermapCounts) :
    wdj_JordanIncrement before after ↔ after.nc = before.nc + 1 := Iff.rfl


end Lattice
end StatMech
