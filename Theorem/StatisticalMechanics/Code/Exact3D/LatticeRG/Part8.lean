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
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG.Part8


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

@[simp] theorem permuteCoordinatesSite_refl {d : ℕ} (x : Site d) :
    permuteCoordinatesSite (Equiv.refl (Fin d)) x = x := by
  rfl

@[simp] theorem permuteCoordinatesSite_trans {d : ℕ}
    (σ τ : Equiv.Perm (Fin d)) (x : Site d) :
    permuteCoordinatesSite τ (permuteCoordinatesSite σ x) =
      permuteCoordinatesSite (σ.trans τ) x := by
  rfl

theorem permuteCoordinatesSite_injective {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    Function.Injective (permuteCoordinatesSite σ) := by
  intro x y hxy
  ext i
  have hcoord := congrFun hxy (σ i)
  simpa [permuteCoordinatesSite] using hcoord


end PolymerSupport
end Exact3D
end StatMech
