/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc60reimerinjection.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc61_boxDoubled_card_invariant (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n) :
    (StatMech.doubleCompress i (StatMech.boxDoubled 𝒜 ℬ)).card
      = (StatMech.boxDoubled 𝒜 ℬ).card :=
  StatMech.doubleCompress_card i _


theorem rc61_boxDoubled_card_le_mul (𝒜 ℬ : Finset (Finset (Fin n))) :
    (StatMech.boxDoubled 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card :=
  StatMech.card_boxDoubled_le_mul 𝒜 ℬ


theorem rc61_boxDoubled_card_eq_dpairs (𝒜 ℬ : Finset (Finset (Fin n))) :
    (StatMech.boxDoubled 𝒜 ℬ).card
      = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card :=
  StatMech.card_boxDoubled 𝒜 ℬ


end StatMech.Walls
