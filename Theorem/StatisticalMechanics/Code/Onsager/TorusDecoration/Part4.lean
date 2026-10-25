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
import Structure.StatisticalMechanics.Code.Onsager.TorusDecoration


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

@[ext] theorem ons_PortPattern.ext {L : ℕ} {P Q : ons_PortPattern L}
    (h : P.bit = Q.bit) : P = Q := by
  cases P
  cases Q
  simp only [ons_PortPattern.mk.injEq]
  exact h

end StatMech.Onsager
