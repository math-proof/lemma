/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part5
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section Reduction

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


section SingleCycle

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


def SingleDualCycleParity (Gp : SimpleGraph V) [DecidableRel Gp.Adj]
    (ψ : Sym2 V ≃ Sym2 V) (cycleSets : Finset (Sym2 V) → Prop) : Prop :=
  ∀ C : Finset (Sym2 V), cycleSets C → EvenOnCycles Gp (C.image ψ.symm)

end SingleCycle
end Reduction
end Ising
end StatMech
