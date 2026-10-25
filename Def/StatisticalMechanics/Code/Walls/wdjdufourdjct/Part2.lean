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
import Structure.StatisticalMechanics.Code.Walls.wdjdufourdjct.Part2
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


attribute [instance] wdj_Hypermap.finD wdj_Hypermap.decD

namespace wdj_HypermapCounts

variable (K : wdj_HypermapCounts)


def wdj_ec : ℤ := K.nv + K.ne + K.nf - K.nd


def wdj_genus : ℤ := K.nc - K.wdj_ec / 2


def wdj_planar : Prop := K.wdj_genus = 0

end wdj_HypermapCounts


def wdj_dufourdFig1 : wdj_HypermapCounts := ⟨15, 7, 6, 6, 3⟩

end Lattice
end StatMech
