/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc13core
import Theorem.StatisticalMechanics.Code.Walls.kc14core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


def kc14_NoSecondBoundedRegion (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ z : Site 2, z ∉ Vc.support → z ∉ jec_leftRegion Vc → ¬ (kc12_component Vc z).Finite


end Walls
end StatMech
