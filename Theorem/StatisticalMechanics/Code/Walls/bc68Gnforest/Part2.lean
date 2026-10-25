/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc67supervertex.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc68Gnforest
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc68_connectedForest_of_GnForestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc68_GnForestData ω L R) : bc65_ConnectedCoarseForest ω L R := by
  obtain ⟨W, _, _, _, G, _, ιU, lamL, hacyc, hmin, hdeg3, hιinj, hlammap, hlaminj⟩ := h
  exact bc68_Gn_spanForest ω L R W G ιU lamL hacyc hmin hdeg3 hιinj hlammap hlaminj


theorem bc68_coarseTcount_le_boundary_of_GnForestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc68_GnForestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc65_coarseTcount_le_boundary_of_connectedForest ω L R
    (bc68_connectedForest_of_GnForestData ω L R h)


theorem bc68_infiniteClusters_top_null_of_GnForestData
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hGnData : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc68_GnForestData ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc67_infiniteClusters_top_null_of_GnForest_route μ hd hinv hfe L
    (fun ω R => bc68_connectedForest_of_GnForestData ω L R (hGnData ω R)) hcoarseRoute


theorem bc68_multiTrif_shared_boundary_survives (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc66_shared_boundary_survives L


theorem bc68_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) (a : Fin 3 → Site d)
      (z : Fin 3 → Site d),
      ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 0) (a 1) →
      ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 0) (a 2) →
      ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 1) (a 2) →
      (∀ i, (bc67_contractedLattice ω L y).Reachable (a i) (z i)) →
      Function.Injective z) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc68_GnForestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    
    (∀ (L : ℕ),
      Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L y a z h01 h02 h12 hreach
    exact bc68_Gn_singleTrif_distinct_leaves ω L y a h01 h02 h12 z hreach
  · intro ω L R h
    exact bc68_coarseTcount_le_boundary_of_GnForestData ω L R h
  · intro L
    exact bc68_multiTrif_shared_boundary_survives L

end StatMech.Walls
