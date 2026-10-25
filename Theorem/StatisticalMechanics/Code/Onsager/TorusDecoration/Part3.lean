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
import Instance.StatisticalMechanics.Code.Onsager.TorusDecoration.Part3


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

theorem ons_decChainCompletion_even_iff (b0 b1 b2 b3 : Fin 2) :
    ons_decChainEven b0 b1 b2 b3 (ons_decChainCompletion b0 b1 b2) ↔
      b0 + b1 + b2 + b3 = 0 := by
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> decide

@[simp] theorem ons_fin2_one_add_eq_zero_iff (x : Fin 2) :
    (1 : Fin 2) + x = 0 ↔ x = 1 := by
  fin_cases x <;> decide

theorem ons_decChain_eq_completion {b0 b1 b2 b3 : Fin 2} {y : Fin 3 → Fin 2}
    (heven : b0 + b1 + b2 + b3 = 0)
    (hy : ons_decChainEven b0 b1 b2 b3 y) :
    y = ons_decChainCompletion b0 b1 b2 := by
  funext k
  fin_cases k <;>
    fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    simp [ons_decChainEven, ons_decChainCompletion] at heven hy ⊢ <;> aesop


theorem ons_decChain_existsUnique (b0 b1 b2 b3 : Fin 2)
    (heven : b0 + b1 + b2 + b3 = 0) :
    ∃! y : Fin 3 → Fin 2, ons_decChainEven b0 b1 b2 b3 y := by
  refine ⟨ons_decChainCompletion b0 b1 b2,
    (ons_decChainCompletion_even_iff b0 b1 b2 b3).mpr heven, ?_⟩
  intro y hy
  exact ons_decChain_eq_completion heven hy

theorem ons_decChainEven_port_even {b0 b1 b2 b3 : Fin 2}
    {y : Fin 3 → Fin 2} (hy : ons_decChainEven b0 b1 b2 b3 y) :
    b0 + b1 + b2 + b3 = 0 := by
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    simp [ons_decChainEven] at hy ⊢ <;> aesop


end StatMech.Onsager
