/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part3
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section K4

abbrev K4 : SimpleGraph (Fin 4) := ⊤

end K4
end Ising
end StatMech
