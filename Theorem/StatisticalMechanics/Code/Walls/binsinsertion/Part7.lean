/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcl2close.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcorcorridors.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Def.StatisticalMechanics.Code.Walls.binsinsertion.Part6
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bins_hroute_of_route (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hres : bins_Route p hp1) :
    ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) →
      ∃ a₁ a₂ a₃ : Site 2,
        0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
  intro n hn
  obtain ⟨I, η₀, a₁, a₂, a₃, X, hne, hadj, hXmeas, hXdep, hXpos, hgeo⟩ := hres n hn
  refine ⟨a₁, a₂, a₃, ?_⟩
  have hindep := bfc2_indep_finite_cofinite p hp1 I
    (bcl_cylinder_measurable I η₀) hXmeas (bcl_cylinder_dependsOn I η₀) hXdep
  exact bdec_precursorPos_of_decoupled p hp1 hp0 hplt a₁ a₂ a₃ I η₀ X hindep hXpos hgeo


theorem bins_bk (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hres : bins_Route p hp1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          {ω | numInfiniteClusters 2 ω ≤ 1} = 1 :=
  bfx_bk_of_route (by norm_num) p hp1 hp0 (bins_hroute_of_route p hp1 hp0 hplt hres)


theorem bins_bk_atLeastTwo (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hres : bins_Route p hp1) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  (bins_bk p hp1 hp0 hplt hres).2.1

end StatMech.Walls
