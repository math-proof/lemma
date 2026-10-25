/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Walls.welenterleave.Part2
import Def.StatisticalMechanics.Code.Walls.wdjdufourdjct.Part2
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


attribute [instance] wdj_Hypermap.finD wdj_Hypermap.decD

theorem wdj_dufourdFig1_chi : wdj_dufourdFig1.wdj_ec = 4 := by decide

theorem wdj_dufourdFig1_genus : wdj_dufourdFig1.wdj_genus = 1 := by decide

theorem wdj_dufourdFig1_not_planar : ¬ wdj_dufourdFig1.wdj_planar := by
  unfold wdj_HypermapCounts.wdj_planar; decide


end Lattice
end StatMech
