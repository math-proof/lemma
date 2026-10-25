/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralShiftDecay.Part2
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose
import Def.StatisticalMechanics.Code.FK.IntegralDecayClose.Part3
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


theorem idc_cylinderAlg_separatesPoints (d : ℕ) :
    (idc_cylinderAlg d).SeparatesPoints := by
  rintro ω₁ ω₂ hne
  obtain ⟨e, he⟩ : ∃ e, ω₁ e ≠ ω₂ e := by
    by_contra hc
    exact hne (funext fun e => not_not.mp (fun h => hc ⟨e, h⟩))
  refine ⟨(idc_coordCM e : ConfigSpace (Sym2 (Site d)) → ℝ),
    ⟨idc_coordCM e, Algebra.subset_adjoin ⟨e, rfl⟩, rfl⟩, ?_⟩
  simp only [idc_coordCM_apply]
  intro hcontra
  apply he
  by_cases h1 : ω₁ e <;> by_cases h2 : ω₂ e <;> simp_all


end FK
end StatMech
