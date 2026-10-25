/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.EsCorrelations.Part3
open scoped BigOperators

set_option linter.style.show false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem card_eqfun_ne {C : Type*} [Fintype C] (q : ℕ) {a b : C} (hab : a ≠ b) :
    Nat.card {f : C → Fin q // f a = f b} = q ^ (Fintype.card C - 1) := by
  classical
  rw [Nat.card_congr (eqFunEquiv q a b hab),
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]


theorem card_eqfun_eq {C : Type*} [Fintype C] (q : ℕ) {a b : C} (hab : a = b) :
    Nat.card {f : C → Fin q // f a = f b} = q ^ Fintype.card C := by
  classical
  subst hab
  have h : {f : C → Fin q // f a = f a} = {f : C → Fin q // True} := by simp
  rw [h, Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)),
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]


end FK
end StatMech
