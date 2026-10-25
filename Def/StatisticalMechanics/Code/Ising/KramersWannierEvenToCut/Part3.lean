/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section ParityConfig

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp : SimpleGraph V) [DecidableRel Gp.Adj] (δ : Finset (Sym2 V))


variable {Gp δ}

variable (Gp δ) in


noncomputable def parityConfig (hG : Gp.Preconnected) (v₀ : V) : ConfigSpace V :=
  fun v => walkParity Gp δ (hG v₀ v).some

end ParityConfig
end Ising
end StatMech
