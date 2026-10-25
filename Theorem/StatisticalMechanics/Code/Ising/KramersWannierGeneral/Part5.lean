/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Def.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section K4Recovery

theorem isingZ_self_dual_K4_via_framework (β βstar : ℝ)
    (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
    isingZ (K4) βstar 0
      = ((2 : ℝ) ^ Fintype.card (Fin 4) * (Real.cosh βstar) ^ (K4).edgeFinset.card
        / (Real.exp (β * (K4).edgeFinset.card) * 2)) * isingZ (K4) β 0 :=
  isingZ_self_dual_of_edgeCrossing K4_preconnected k4EdgeCrossing β βstar htemp

end K4Recovery
end Ising
end StatMech
