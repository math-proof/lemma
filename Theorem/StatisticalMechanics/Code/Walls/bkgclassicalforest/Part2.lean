/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bgfacyclicstep
import Theorem.StatisticalMechanics.Code.Walls.bararmray
import Theorem.StatisticalMechanics.Code.Walls.bc69count.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkwburtonkeane
import Def.StatisticalMechanics.Code.Walls.bkgclassicalforest.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bkg_globalForest_of_classical (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bkg_ClassicalForestData ω L R) : bc69_Gn_globalForest ω L R := by
  obtain ⟨S, hSfin, hSne, G, hGdec, Amb, ιU, hle, H1, hmin, hdeg3, hιinj, hbdry⟩ := h
  exact ⟨S, hSfin, hSne, G, hGdec, ιU,
    bkg_acyclic_of_singleVertexCut Amb G hle H1, hmin, hdeg3, hιinj, hbdry⟩


theorem bkg_coarseTcount_of_classical (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bkg_ClassicalForestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc69_coarseTcount_le_boundary ω L R (bkg_globalForest_of_classical ω L R h)


theorem bkg_bc69_of_classical (L R : ℕ)
    (hdata : ∀ ω : ConfigSpace (Sym2 (Site d)), bkg_ClassicalForestData ω L R) :
    ∀ ω : ConfigSpace (Sym2 (Site d)), bc69_Gn_globalForest ω L R :=
  fun ω => bkg_globalForest_of_classical ω L R (hdata ω)


theorem bkg_bk_uniqueness_of_classical (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          {ω | numInfiniteClusters 2 ω ≤ 1} = 1 :=
  bkw_bk_uniqueness_of_forest p hp1 hp0
    (fun ω L R => bkg_globalForest_of_classical ω L R (hdata ω L R))


theorem bkg_top_null_of_classical (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
  bkw_top_null_of_forest p hp1 hp0
    (fun ω L R => bkg_globalForest_of_classical ω L R (hdata ω L R))


theorem bkg_status :
    
    (∀ {V : Type} (Amb G : SimpleGraph V), G ≤ Amb →
      (∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → ¬ (bkg_deleteVertex Amb t).Reachable a b) →
      G.IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bkg_ClassicalForestData ω L R → bc69_Gn_globalForest ω L R) ∧
    
    (∀ (p : NNReal) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V Amb G hle H1; exact bkg_acyclic_of_singleVertexCut Amb G hle H1
  · intro ω L R h; exact bkg_globalForest_of_classical ω L R h
  · intro p hp1 hp0 hdata; exact (bkg_bk_uniqueness_of_classical p hp1 hp0 hdata).2.1

end StatMech.Walls
