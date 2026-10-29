/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bclclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bpt2corridors.Part4
import Theorem.StatisticalMechanics.Code.Walls.bfc2indep
import Theorem.StatisticalMechanics.Code.Walls.bdecdecouple
import Theorem.StatisticalMechanics.Code.Walls.bfxtrifexist
import Def.StatisticalMechanics.Code.Walls.bclclose
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bcl_hroute_of_residue (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hres : bcl_ArmResidue p hp1) :
    ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) →
        ∃ a₁ a₂ a₃ : Site 2,
          0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
            (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
  intro n htop
  obtain ⟨I, a₁, a₂, a₃, x₁, x₂, x₃, η₀, hne, hadj, hcorr, hExtMeas, hXpos⟩ := hres n htop
  exact ⟨a₁, a₂, a₃,
    bcl_precursorPos p hp1 hp0 hplt I a₁ a₂ a₃ x₁ x₂ x₃ η₀ hne hadj hcorr hExtMeas hXpos⟩


theorem bcl_bk (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hres : bcl_ArmResidue p hp1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          {ω | numInfiniteClusters 2 ω ≤ 1} = 1 :=
  bfx_bk_of_route (by norm_num) p hp1 hp0 (bcl_hroute_of_residue p hp1 hp0 hplt hres)


theorem bcl_bk_atLeastTwo (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hres : bcl_ArmResidue p hp1) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  (bcl_bk p hp1 hp0 hplt hres).2.1

end StatMech.Walls
