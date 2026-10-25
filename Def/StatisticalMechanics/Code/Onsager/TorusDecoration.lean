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


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

def ons_decInternalAdj {L : ℕ} (d e : ons_Dart L) : Prop :=
  d.1 = e.1 ∧ (d.2.val + 1 = e.2.val ∨ e.2.val + 1 = d.2.val)

def ons_decAdj (L : ℕ) (d e : ons_Dart L) : Prop :=
  e = ons_dartRev L d ∨ ons_decInternalAdj d e

end StatMech.Onsager
