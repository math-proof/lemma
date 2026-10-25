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
import Instance.StatisticalMechanics.Code.Onsager.TorusDecoration


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

theorem ons_decAdj_symm (L : ℕ) : Symmetric (ons_decAdj L) := by
  intro d e h
  rcases h with hrev | hint
  · left
    rw [hrev, ons_dartRev_involutive]
  · right
    exact ⟨hint.1.symm, hint.2.symm⟩

theorem ons_dartRev_ne_self (L : ℕ) (d : ons_Dart L) :
    ons_dartRev L d ≠ d := by
  intro h
  have hdir := congrArg Prod.snd h
  rcases d with ⟨s, mu⟩
  simp only [ons_dartRev] at hdir
  fin_cases mu <;> simp at hdir

end StatMech.Onsager
