/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7


namespace StatMech.FrontierA

open SimpleGraph StatMech.Onsager

theorem triangularTorusDirectionStep_injective
    (L : Nat) [Fact (2 < L)] :
    Function.Injective (triangularTorusDirectionStep L) := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
    exact one_ne_zero
  have h2 : (2 : ZMod L) ≠ 0 := by
    rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have := (Fact.out : 2 < L)
    omega
  have hm1 : (-1 : ZMod L) ≠ 0 := neg_ne_zero.mpr h1
  have hpm : (1 : ZMod L) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have h01 : (0 : ZMod L) ≠ 1 := Ne.symm h1
  have hmp : (-1 : ZMod L) ≠ 1 := Ne.symm hpm
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionStep, h1, hm1, hpm, h01, hmp] at hab ⊢

theorem triangularTorusDart_adj
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) (a : Fin 6) :
    (triangularTorusGraph L).Adj p
      (p - triangularTorusDirectionStep L a) := by
  fin_cases a <;>
    simp [triangularTorusGraph, triangularTorusAdj, onsTorusAdj,
      triangularTorusDirectionStep] <;> ring


end StatMech.FrontierA
