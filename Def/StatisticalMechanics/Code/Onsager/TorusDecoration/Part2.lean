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
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

def ons_decGraph (L : ℕ) : SimpleGraph (ons_Dart L) where
  Adj := ons_decAdj L
  symm := ons_decAdj_symm L
  loopless := by
    refine ⟨?_⟩
    intro d hd
    rcases hd with hrev | hint
    · exact ons_dartRev_ne_self L d hrev.symm
    · rcases hint.2 with h | h <;> omega

end StatMech.Onsager
