/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section K4Recovery

def k4CompEquiv : Sym2 (Fin 4) ≃ Sym2 (Fin 4) :=
  Function.Involutive.toPerm k4Comp k4Comp_involutive

end K4Recovery
end Ising
end StatMech
