/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part5
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem exists_isLoewnerAdmissibleDuration {W : ℝ → ℝ} (hW : Continuous W)
    {z : ℂ} (hz : 0 < z.im) : ∃ T, IsLoewnerAdmissibleDuration W z T := by
  obtain ⟨T, hT, g, hg0, hgd, hgu⟩ := loewner_local_existence hW hz
  exact ⟨T, hT, ⟨⟨g, hg0, hgd, hgu⟩⟩⟩


theorem IsLoewnerAdmissibleDuration.mono {W : ℝ → ℝ} {z : ℂ} {S T : ℝ}
    (hT : IsLoewnerAdmissibleDuration W z T) (hS : 0 < S) (hST : S ≤ T) :
    IsLoewnerAdmissibleDuration W z S := by
  rcases hT with ⟨_, ⟨g⟩⟩
  exact ⟨hS, ⟨g.restrict hST⟩⟩


end StatMech.SLE
