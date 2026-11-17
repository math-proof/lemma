/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
public import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
public import Theorem.StatisticalMechanics.Code.Onsager.Torus
public import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part3


public section

namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

structure ons_PortPattern (L : ℕ) where
  bit : ons_Dart L → Fin 2
  rev_bit : ∀ d, bit (ons_dartRev L d) = bit d
  site_even : ∀ s : ZMod L × ZMod L,
    bit (s, 0) + bit (s, 1) + bit (s, 2) + bit (s, 3) = 0

end StatMech.Onsager
