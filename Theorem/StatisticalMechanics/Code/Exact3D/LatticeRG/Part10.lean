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
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG.Part10


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

theorem coordinateRadiusBound_blockRemainder {d : ℕ}
    (scale : BlockScale) (x : Site d) :
    coordinateRadiusBound (scale.L - 1) (blockRemainder scale x) := by
  intro i
  exact Nat.le_pred_of_lt (blockRemainder_natAbs_lt_scale scale x i)

@[simp] theorem coordinateRadiusBound_iff_mem_box {d R : ℕ} {x : Site d} :
    coordinateRadiusBound R x ↔ x ∈ box d R :=
  Iff.rfl

theorem coordinateRadiusBound_mono {d R S : ℕ} {x : Site d}
    (hRS : R ≤ S) (hx : coordinateRadiusBound R x) :
    coordinateRadiusBound S x := by
  intro i
  exact le_trans (hx i) hRS

theorem coordinateRadiusBound_add {d R S : ℕ} {x y : Site d}
    (hx : coordinateRadiusBound R x) (hy : coordinateRadiusBound S y) :
    coordinateRadiusBound (R + S) (x + y) := by
  intro i
  exact le_trans (Int.natAbs_add_le (x i) (y i))
    (Nat.add_le_add (hx i) (hy i))


theorem coordinateRadiusBound_permuteCoordinatesSite {d R : ℕ}
    {x : Site d} (σ : Equiv.Perm (Fin d))
    (hx : coordinateRadiusBound R x) :
    coordinateRadiusBound R (permuteCoordinatesSite σ x) := by
  intro i
  exact hx (σ.symm i)


end PolymerSupport
end Exact3D
end StatMech
