/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Def.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section K4Recovery

theorem k4Comp_involutive (e : Sym2 (Fin 4)) : k4Comp (k4Comp e) = e := by
  revert e; decide


end K4Recovery
end Ising
end StatMech
