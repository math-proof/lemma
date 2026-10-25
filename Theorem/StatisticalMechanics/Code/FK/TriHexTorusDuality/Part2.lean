/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.FK.TriHexTorusDuality
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem triangularTorusStep_ne_zero (L : ℕ) [Fact (2 < L)] (i : Fin 3) :
    triangularTorusStep L i ≠ 0 := by
  fin_cases i <;> intro h
  · exact zmod_one_ne_zero L (congrArg Prod.fst h)
  · exact zmod_one_ne_zero L (congrArg Prod.snd h)
  · exact zmod_one_ne_zero L (by
      have hs := congrArg Prod.snd h
      simpa [triangularTorusStep] using hs)

theorem triangularTorusStep_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (triangularTorusStep L) := by
  have h1 := zmod_one_ne_zero L
  have h2 := zmod_two_ne_zero L
  have hm : (1 : ZMod L) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [triangularTorusStep]

theorem triangularTorusStep_add_ne_zero (L : ℕ) [Fact (2 < L)]
    (i j : Fin 3) :
    triangularTorusStep L i + triangularTorusStep L j ≠ 0 := by
  have h1 := zmod_one_ne_zero L
  have h2 := zmod_two_ne_zero L
  fin_cases i <;> fin_cases j <;> intro h <;>
    simp only [triangularTorusStep, Nat.succ_eq_add_one, Nat.reduceAdd,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Prod.mk_add_mk, Prod.mk_eq_zero, add_zero, zero_add, add_neg_cancel,
      neg_add_cancel, and_true, true_and, and_self, neg_eq_zero] at h
  all_goals first
    | exact h2 (by linear_combination h)
    | exact h2 (by linear_combination -h.1)
    | exact h2 (by linear_combination -h.2)
    | exact h1 (by linear_combination h)
    | exact h2 h.1
    | exact h2 h.2
    | exact h1 h.1

theorem hexagonalTorusStep_ne_zero (L : ℕ) [Fact (2 < L)] (i : Fin 3) :
    hexagonalTorusStep L i ≠ 0 := by
  fin_cases i <;> intro h
  · exact zmod_one_ne_zero L (congrArg Prod.fst h)
  · exact zmod_one_ne_zero L (congrArg Prod.snd h)
  · exact zmod_one_ne_zero L (congrArg Prod.fst h)

theorem hexagonalTorusStep_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (hexagonalTorusStep L) := by
  have h1 := zmod_one_ne_zero L
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [hexagonalTorusStep]


end PeriodicPlanar
end FK
end StatMech
