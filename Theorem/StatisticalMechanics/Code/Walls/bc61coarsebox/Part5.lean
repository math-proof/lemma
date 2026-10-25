/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc60upperlines.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc54coarse
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc61coarsebox.Part5
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc61_infiniteClusters_top_null_of_coarse
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R)
    (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  have hprob0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 :=
    bc61_coarseTrif_prob_eq_zero μ L bdry hexp hbound hvol hdens
  by_contra htop
  have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr htop
  have := hexist hpos
  rw [hprob0] at this
  exact lt_irrefl 0 this


theorem bc61_status :
    
    (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) ∧
    (∀ {L : ℕ}, 3 ≤ L →
      (∀ (G : Finset (Sym2 (Site 2))) (a a' : Site 2), a 1 ≤ 1 → a' 1 ≤ 1 →
        (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite →
        (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a').Infinite →
        Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a a')) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bc61_CoarseForestLeafCount ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) :=
  ⟨fun hL => bc61_wholeBox_severs_upperLines hL,
   fun _hL _G _a _a' ha ha' hi hi' => bc61_singleSite_fails_upperLines ha ha' hi hi',
   fun ω L R h => bc61_coarseTcount_le_boundary_of_forest ω L R h⟩

end StatMech.Walls
