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
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part3


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

structure ons_PortPattern (L : ℕ) where
  bit : ons_Dart L → Fin 2
  rev_bit : ∀ d, bit (ons_dartRev L d) = bit d
  site_even : ∀ s : ZMod L × ZMod L,
    bit (s, 0) + bit (s, 1) + bit (s, 2) + bit (s, 3) = 0

end StatMech.Onsager
