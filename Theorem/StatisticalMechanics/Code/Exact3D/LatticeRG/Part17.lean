/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Structure.StatisticalMechanics.Code.Exact3D.LatticeRG.Part3


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace LatticeRGData

variable {d : ℕ}

@[simp] theorem kernel_scale_eq_R_scale (G : LatticeRGData d) :
    G.kernel.scale = G.R.scale :=
  G.scale_match

theorem R_scale_eq_kernel_scale (G : LatticeRGData d) :
    G.R.scale = G.kernel.scale :=
  G.scale_match.symm

@[simp] theorem kernel_scale_toReal_eq_R_scale_toReal
    (G : LatticeRGData d) :
    G.kernel.scale.toReal = G.R.scale.toReal := by
  exact congrArg BlockScale.toReal G.kernel_scale_eq_R_scale

theorem R_scale_toReal_eq_kernel_scale_toReal
    (G : LatticeRGData d) :
    G.R.scale.toReal = G.kernel.scale.toReal := by
  exact congrArg BlockScale.toReal G.R_scale_eq_kernel_scale

end LatticeRGData
end Exact3D
end StatMech
