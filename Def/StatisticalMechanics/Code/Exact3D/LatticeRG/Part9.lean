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
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part8


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

def permuteCoordinates {d : ℕ} (P : PolymerSupport d)
    (σ : Equiv.Perm (Fin d)) : PolymerSupport d where
  carrier := P.carrier.image (permuteCoordinatesSite σ)

end PolymerSupport
end Exact3D
end StatMech
