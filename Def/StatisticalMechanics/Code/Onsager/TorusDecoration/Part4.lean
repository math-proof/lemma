/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part2


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

def ons_decChainCompletion (b0 b1 b2 : Fin 2) : Fin 3 → Fin 2 :=
  ![b0, b0 + b1, b0 + b1 + b2]

def ons_decChainEven (b0 b1 b2 b3 : Fin 2) (y : Fin 3 → Fin 2) : Prop :=
  b0 + y 0 = 0 ∧
  b1 + y 0 + y 1 = 0 ∧
  b2 + y 1 + y 2 = 0 ∧
  b3 + y 2 = 0

end StatMech.Onsager
