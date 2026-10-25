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
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG


namespace StatMech

namespace Exact3D

open StatMech.Lattice


@[simp] theorem blockRepresentative_apply {d : ℕ} (scale : BlockScale)
    (b : BlockIndex d) (i : Fin d) :
    blockRepresentative scale b i = (scale.L : ℤ) * b i :=
  rfl

@[simp] theorem blockRepresentative_zero {d : ℕ} (scale : BlockScale) :
    blockRepresentative scale (0 : BlockIndex d) = (0 : Site d) := by
  ext i
  simp [blockRepresentative]

@[simp] theorem blockIndexOf_blockRepresentative {d : ℕ}
    (scale : BlockScale) (b : BlockIndex d) :
    blockIndexOf scale (blockRepresentative scale b) = b := by
  ext i
  simpa [blockIndexOf, blockRepresentative] using
    Int.mul_ediv_cancel_left (b i) (Int.ofNat_ne_zero.mpr scale.L_ne_zero)

@[simp] theorem blockIndexOf_zero {d : ℕ} (scale : BlockScale) :
    blockIndexOf scale (0 : Site d) = (0 : BlockIndex d) := by
  ext i
  simp [blockIndexOf]


end Exact3D
end StatMech
