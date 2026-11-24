module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Walls.welenterleave.Part2
public import Def.StatisticalMechanics.Code.Walls.wdjdufourdjct.Part3
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

theorem wdj_sphereExample_planar : wdj_sphereExample.wdj_planar := by
  unfold wdj_HypermapCounts.wdj_planar; decide

theorem wdj_sphereExample_eulerFormula : wdj_sphereExample.wdj_ec = 2 := by decide

theorem wdj_sphereExample_euler_eq_nc :
    wdj_sphereExample.wdj_ec / 2 = wdj_sphereExample.nc := by decide


end Lattice
end StatMech
