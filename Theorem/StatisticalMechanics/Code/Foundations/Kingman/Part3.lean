/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Foundations.Kingman.Part2
open MeasureTheory Filter Topology


namespace StatMech

namespace Kingman

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}


namespace SubadditiveCocycle

variable {T : α → α} {X : ℕ → α → ℝ}


theorem tendsto_expSeq_div (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => expSeq X μ n / n)) :
    Tendsto (fun n => expSeq X μ n / n) atTop (𝓝 (gamma h)) :=
  (subadditive_expSeq h).tendsto_lim hbdd


theorem gamma_le_div (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => expSeq X μ n / n)) {n : ℕ} (hn : n ≠ 0) :
    gamma h ≤ expSeq X μ n / n :=
  (subadditive_expSeq h).lim_le_div hbdd hn


theorem gamma_le_expSeq_one (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => expSeq X μ n / n)) :
    gamma h ≤ expSeq X μ 1 := by
  refine le_trans (gamma_le_div h hbdd (n := 1) one_ne_zero) ?_
  simp


theorem bddBelow_of_nonneg (_h : SubadditiveCocycle T μ X)
    (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    BddBelow (Set.range fun n => expSeq X μ n / n) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hX : 0 ≤ expSeq X μ n := integral_nonneg_of_ae (hnn n)
  positivity

end SubadditiveCocycle
end Kingman
end StatMech
