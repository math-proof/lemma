/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section ParityConfig

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp : SimpleGraph V) [DecidableRel Gp.Adj] (δ : Finset (Sym2 V))


def EvenOnCycles : Prop := ∀ (x : V) (p : Gp.Walk x x), walkParity Gp δ p = false

end ParityConfig
end Ising
end StatMech
