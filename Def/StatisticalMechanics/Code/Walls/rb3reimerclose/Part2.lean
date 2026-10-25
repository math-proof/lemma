/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rb2butterflyclose.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc86consolidation
import Theorem.StatisticalMechanics.Code.Walls.rb3reimerclose
open Finset
open scoped BigOperators NNReal


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false

set_option linter.unusedSimpArgs false


open Classical in


noncomputable def rb3_witK {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Fin n) := by
  classical
  exact if h : ∃ K L : Finset (Fin n), Disjoint K L ∧
      (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ)
    then h.choose else ∅

end StatMech.Walls.Reimer
