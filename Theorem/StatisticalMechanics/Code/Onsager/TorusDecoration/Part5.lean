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
import Def.StatisticalMechanics.Code.Onsager.TorusDecoration.Part5


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

theorem ons_decNeighborBit_symm {L : ℕ} (P : ons_PortPattern L)
    (d e : ons_Dart L) :
    ons_decNeighborBit P d e = ons_decNeighborBit P e d := by
  by_cases hrev : e = ons_dartRev L d
  · subst e
    have hinv : ons_dartRev L (ons_dartRev L d) = d :=
      ons_dartRev_involutive L d
    rw [ons_decNeighborBit, if_pos rfl, ons_decNeighborBit,
      if_pos hinv.symm, P.rev_bit]
  · have hrev' : d ≠ ons_dartRev L e := by
      intro h
      apply hrev
      rw [h, ons_dartRev_involutive]
    rw [ons_decNeighborBit, if_neg hrev, ons_decNeighborBit, if_neg hrev']
    by_cases hs : d.1 = e.1
    · rw [if_pos hs, if_pos hs.symm]
      rcases d with ⟨s, mu⟩
      rcases e with ⟨t, nu⟩
      simp only [Prod.mk.injEq] at hs
      subst t
      fin_cases mu <;> fin_cases nu <;> rfl
    · rw [if_neg hs, if_neg (Ne.symm hs)]

end StatMech.Onsager
