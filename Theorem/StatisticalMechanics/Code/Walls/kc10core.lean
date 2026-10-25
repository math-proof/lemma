/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc9core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc10_collar_up (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hzoff : z ∉ Vc.support) (hupOff : (![z 0, z 1 + 1] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z ![z 0, z 1 + 1] :=
  kc9_upStep Vc hzoff hupOff


end Walls
end StatMech
