/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
open MeasureTheory Set
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.ConfigSpace


section TranslationInvariance

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


theorem shift_eq_piCongrLeft (g : G) :
    (shift g : ConfigSpace E → ConfigSpace E)
      = ⇑(Equiv.piCongrLeft (fun _ : E => Bool) (MulAction.toPerm g)) := by
  funext ω b
  set e₁ := MulAction.toPerm (β := E) g with he₁
  conv_rhs => rw [show b = e₁ (e₁.symm b) from (e₁.apply_symm_apply b).symm,
    Equiv.piCongrLeft_apply_apply (a := e₁.symm b)]
  rw [shift_apply, he₁, MulAction.toPerm_symm_apply]


theorem bernoulli_translationInvariant (p : NNReal) (hp : p ≤ 1) [Countable E] :
    IsTranslationInvariant (G := G) (bernoulliProductMeasure (E := E) p hp) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  rw [shift_eq_piCongrLeft]
  have h := Measure.infinitePi_map_piCongrLeft (μ := fun _ : E => bernoulliMeasure p hp)
    (MulAction.toPerm (β := E) g)
  simpa only [bernoulliProductMeasure] using h

end TranslationInvariance
end Percolation
end StatMech
