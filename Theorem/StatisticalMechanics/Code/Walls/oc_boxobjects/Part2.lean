/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
import Theorem.StatisticalMechanics.Code.FK.FKQ2Sharp
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Walls.oc_boxobjects.Part2
open scoped BigOperators
open Finset Set
open scoped Classical

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace Walls

open StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]


section Bundle

variable (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]

variable (Af : ℕ → Set (ConfigSpace (Sym2 V))) (hAf : ∀ n, IsIncreasing (Af n))


theorem oc_boxFamily_theta (n : ℕ) (β : ℝ) :
    (oc_boxFamily Gf Af hAf).theta n β = oc_theta Gf Af n β := rfl


theorem oc_boxFamily_S (n : ℕ) (β : ℝ) :
    (oc_boxFamily Gf Af hAf).S n β = oc_S Gf Af n β := rfl


theorem oc_boxFamily_S_eq_sum (n : ℕ) (β : ℝ) :
    (oc_boxFamily Gf Af hAf).S n β
      = ∑ k ∈ Finset.range n, (oc_boxFamily Gf Af hAf).theta k β := rfl


theorem oc_boxFamily_theta_mem_Icc {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    (oc_boxFamily Gf Af hAf).theta n β ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(oc_boxFamily Gf Af hAf).theta_nonneg hβ hβ1 n,
   (oc_boxFamily Gf Af hAf).theta_le_one hβ hβ1 n⟩


theorem oc_boxFamily_theta_mono (n : ℕ) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₂1 : β₂ < 1) (hle : β₁ ≤ β₂) :
    (oc_boxFamily Gf Af hAf).theta n β₁ ≤ (oc_boxFamily Gf Af hAf).theta n β₂ :=
  (oc_boxFamily Gf Af hAf).theta_mono n hβ₁ hβ₂1 hle

end Bundle
end Walls
end StatMech
