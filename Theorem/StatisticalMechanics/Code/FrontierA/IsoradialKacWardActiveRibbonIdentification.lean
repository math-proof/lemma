/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardActiveRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardActiveRibbonIdentification


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


theorem finiteCRSFFormanProduct_eq_zero_of_twoCycle
    (transport : V -> V -> Complex) (next : V -> V) {v w : V}
    (hvw : v ≠ w) (hnextv : next v = w) (hnextw : next w = v)
    (htransport : transport v w * transport w v = 1) :
    finiteCRSFFormanProduct transport next = 0 := by
  let cycle : finiteCRSFAtomicCycle next :=
    ⟨Equiv.swap v w, Equiv.Perm.isCycle_swap hvw, by
      intro u hu
      rw [Equiv.Perm.support_swap hvw] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · simpa [hvw] using hnextv.symm
      · simpa [hvw] using hnextw.symm⟩
  unfold finiteCRSFFormanProduct
  apply Finset.prod_eq_zero (Finset.mem_univ cycle)
  rw [sub_eq_zero]
  unfold finiteCRSFAmbientAtomicCycleHolonomy
  rw [Equiv.Perm.support_swap hvw]
  rw [Finset.prod_insert (fun h => hvw (Finset.mem_singleton.mp h)),
    Finset.prod_singleton,
    hnextv, hnextw, htransport]


end StatMech.FrontierA
