/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rb2butterflyclose.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc86consolidation
import Theorem.StatisticalMechanics.Code.Walls.rb3reimerclose.Part2
open Finset
open scoped BigOperators NNReal


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false

set_option linter.unusedSimpArgs false


noncomputable def rb3_body {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) (x : rbt_Q n) : rbt_Q n :=
  rb3_toB (rc36_R0 (rb3_ofB x) (rb3_witK 𝒜 ℬ (rb3_ofB x)) (rb3_witK 𝒜 ℬ (rb3_ofB x))ᶜ)


end StatMech.Walls.Reimer
