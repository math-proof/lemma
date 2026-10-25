/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFKBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling.Part2
open MeasureTheory Set


namespace StatMech

namespace FrontierB

open ConfigSpace FK Lattice

variable {d : ℕ}

section FiniteEdwardsSokal

open Potts

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def esCoeffOpen {q : ℕ} (p : ℝ) (sigma : V → Fin q)
    (target e : Sym2 V) (b : Bool) : ℝ :=
  esCoeff G p sigma e b *
    if e = target then (if b then 1 else 0) else 1

end FiniteEdwardsSokal
end FrontierB
end StatMech
