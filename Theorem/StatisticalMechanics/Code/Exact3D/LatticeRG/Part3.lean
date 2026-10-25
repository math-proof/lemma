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
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG.Part3


namespace StatMech

namespace Exact3D

open StatMech.Lattice


theorem deterministicKernel_allowed {d : ℕ} (scale : BlockScale)
    (coarse : ConfigSpace (Site d) → ConfigSpace (BlockIndex d))
    (σ : ConfigSpace (Site d)) :
    (deterministicKernel scale coarse).allowed σ (coarse σ) := by
  rfl

@[simp] theorem deterministicKernel_allowed_iff {d : ℕ} (scale : BlockScale)
    (coarse : ConfigSpace (Site d) → ConfigSpace (BlockIndex d))
    (σ : ConfigSpace (Site d)) (τ : ConfigSpace (BlockIndex d)) :
    (deterministicKernel scale coarse).allowed σ τ ↔ τ = coarse σ :=
  Iff.rfl


end Exact3D
end StatMech
