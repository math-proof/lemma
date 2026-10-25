/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
open StatMech ConfigSpace
open scoped BigOperators Pointwise


namespace StatMech

namespace FK

variable {E : Type*}


section Representatives

variable [DecidableEq E]


lemma repOf_agree (S : Finset E) (φ : ↥S → Bool) {e : E} (he : e ∈ S) :
    repOf S φ e = φ ⟨e, he⟩ := by
  simp only [repOf, dif_pos he]


theorem indicator_eq_sum_cyl (C : Set (ConfigSpace E)) (S : Finset E)
    (hC : DependsOn (C.indicator (1 : ConfigSpace E → ℝ)) (S : Set E)) :
    C.indicator (1 : ConfigSpace E → ℝ)
      = ∑ φ : ↥S → Bool,
          (C.indicator (1 : ConfigSpace E → ℝ) (repOf S φ)) •
            (cyl S (repOf S φ)).indicator 1 := by
  ext ω
  rw [Finset.sum_apply,
    Finset.sum_eq_single_of_mem (fun i : ↥S => ω i.1) (Finset.mem_univ _)]
  · have hmem : ω ∈ cyl S (repOf S (fun i : ↥S => ω i.1)) := by
      intro e he; rw [repOf_agree S _ he]
    rw [Pi.smul_apply, Set.indicator_of_mem hmem, Pi.one_apply, smul_eq_mul, mul_one]
    refine hC ?_
    intro e he
    rw [repOf_agree S _ he]
  · intro φ _ hne
    have hnmem : ω ∉ cyl S (repOf S φ) := by
      intro hmem
      apply hne
      funext i
      have hh := hmem i.1 i.2
      rw [repOf_agree S φ i.2] at hh
      rw [hh]
    rw [Pi.smul_apply, Set.indicator_of_notMem hnmem, smul_zero]


theorem indicator_signedIncreasingCombo_of_dependsOn
    (C : Set (ConfigSpace E)) (S : Finset E)
    (hC : DependsOn (C.indicator (1 : ConfigSpace E → ℝ)) (S : Set E)) :
    SignedIncreasingCombo (C.indicator (1 : ConfigSpace E → ℝ)) := by
  rw [SignedIncreasingCombo, indicator_eq_sum_cyl C S hC]
  refine Submodule.sum_mem _ fun φ _ => Submodule.smul_mem _ _ ?_
  exact cyl_indicator_signedIncreasingCombo S (repOf S φ)

end Representatives
end FK
end StatMech
