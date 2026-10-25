/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part2
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

theorem pair_with_localEdgeFlip_eq_closed_add_open
    (e : Sym2 P.V) (f : ConfigSpace (Sym2 P.V) -> Complex)
    (omega : ConfigSpace (Sym2 P.V)) :
    f omega + f (localEdgeFlipEquiv e omega) =
      f (setClosed e omega) + f (setOpen e omega) := by
  cases h : omega e with
  | false =>
      have hclosed : setClosed e omega = omega := by
        funext e'
        by_cases he' : e' = e
        · subst e'
          simp [h]
        · rw [setClosed_of_ne he']
      have hflip : localEdgeFlipEquiv e omega = setOpen e omega := by
        unfold localEdgeFlipEquiv localEdgeFlip setOpen
        simp [h]
      rw [hclosed, hflip]
  | true =>
      have hopen : setOpen e omega = omega := by
        funext e'
        by_cases he' : e' = e
        · subst e'
          simp [h]
        · rw [setOpen_of_ne he']
      have hflip : localEdgeFlipEquiv e omega = setClosed e omega := by
        unfold localEdgeFlipEquiv localEdgeFlip setClosed
        simp [h]
      rw [hopen, hflip, add_comm]


end FKIsingDobrushinDomain
end
end StatMech.Universality
