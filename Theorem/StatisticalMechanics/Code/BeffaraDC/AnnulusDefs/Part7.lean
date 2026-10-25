/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part7
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

@[simp] theorem diagReflIso_apply (x : Site 2) : diagReflIso x = diagReflFun x := rfl


end BeffaraDC
end StatMech
