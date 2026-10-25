/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.CardyDiscreteHolo.Part3


namespace StatMech.Universality

open Complex


namespace CardyLocalConfig

attribute [instance] CardyLocalConfig.fin

variable (L : CardyLocalConfig)


theorem cardyS_eq_combination :
    L.cardyS = L.crossingFun 0 + cardyOmega * L.crossingFun 1
        + cardyOmega ^ 2 * L.crossingFun 2 := by
  unfold cardyS crossingFun
  
  rw [← Finset.sum_fiberwise Finset.univ L.arc (fun ω => cardyWpow (L.arc ω) * L.weight ω)]
  
  have hfib : ∀ j : ZMod 3,
      (∑ ω ∈ Finset.univ.filter (fun ω => L.arc ω = j),
          cardyWpow (L.arc ω) * L.weight ω)
        = cardyWpow j * ∑ ω ∈ Finset.univ.filter (fun ω => L.arc ω = j), L.weight ω := by
    intro j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [Finset.mem_filter] at hω
    rw [hω.2]
  
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [hfib 0, hfib 1, hfib 2, cardyWpow_zero, cardyWpow_one, cardyWpow_two]
  ring


theorem colorSwap_S_zero : L.cardyS = 0 := by
  
  have hself : L.cardyS = cardyOmega * L.cardyS := by
    calc L.cardyS
        = ∑ ω, cardyWpow (L.arc (L.rot ω)) * L.weight (L.rot ω) := by
          unfold cardyS
          exact (Fintype.sum_bijective L.rot L.rot_bij _ _ (fun ω => rfl)).symm
      _ = ∑ ω, cardyOmega * (cardyWpow (L.arc ω) * L.weight ω) := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [L.arc_rot, L.weight_rot, cardyWpow_succ]; ring
      _ = cardyOmega * L.cardyS := by rw [cardyS, Finset.mul_sum]
  have hfac : (1 - cardyOmega) * L.cardyS = 0 := by
    rw [sub_mul, one_mul, ← hself, sub_self]
  have h1w : (1 : ℂ) - cardyOmega ≠ 0 :=
    sub_ne_zero.mpr (fun h => cardyOmega_ne_one h.symm)
  exact (mul_eq_zero.mp hfac).resolve_left h1w


theorem crossingCombination_zero :
    L.crossingFun 0 + cardyOmega * L.crossingFun 1
        + cardyOmega ^ 2 * L.crossingFun 2 = 0 := by
  rw [← cardyS_eq_combination]; exact L.colorSwap_S_zero

end CardyLocalConfig
end StatMech.Universality
