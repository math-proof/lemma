/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part5
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteStarEdge_injective (n : Nat) :
    Function.Injective (triHexPlanarFiniteStarEdge n) := by
  rintro ⟨z, i⟩ ⟨w, j⟩ h
  change s(Sum.inl z,
      Sum.inr (triHexPlanarFiniteTerminalMap n z i)) =
    s(Sum.inl w,
      Sum.inr (triHexPlanarFiniteTerminalMap n w j)) at h
  rw [Sym2.eq_iff] at h
  rcases h with hdir | hswap
  · have hzw : z = w := Sum.inl.inj hdir.1
    subst w
    have ht : triHexPlanarFiniteTerminalMap n z i =
        triHexPlanarFiniteTerminalMap n z j := Sum.inr.inj hdir.2
    have hsite := congrArg Subtype.val ht
    have hstep : hexagonalStep i = hexagonalStep j := by
      exact add_left_cancel hsite
    exact Prod.ext rfl (hexagonalStep_injective hstep)
  · exact (Sum.inl_ne_inr hswap.1).elim


end
end StatMech.FK.PeriodicPlanar
