/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Def.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section ParityConfig

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp : SimpleGraph V) [DecidableRel Gp.Adj] (δ : Finset (Sym2 V))


variable {Gp δ}

omit [Fintype V] [DecidableRel Gp.Adj] in


theorem walkParity_eq_of_evenOnCycles (hev : EvenOnCycles Gp δ) {x y : V}
    (p q : Gp.Walk x y) : walkParity Gp δ p = walkParity Gp δ q := by
  
  have hclosed : walkParity Gp δ (p.append q.reverse) = false := hev _ _
  rw [walkParity_append, walkParity_reverse] at hclosed
  
  revert hclosed
  cases walkParity Gp δ p <;> cases walkParity Gp δ q <;> simp

end ParityConfig
end Ising
end StatMech
