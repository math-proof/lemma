/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/blfboundaryleaf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bof2leafcount.Part2
import Def.StatisticalMechanics.Code.Walls.blfboundaryleaf
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


theorem blf_bc69_of_acyclicArmUnion (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : blf_AcyclicArmUnion ω L R) : bc69_Gn_globalForest ω L R := by
  obtain ⟨S, hSfin, hSne, G, hGdec, ιU, hac, hmin, hdeg3, hinj, hint⟩ := h
  exact blf_bc69_of_interiorDeg2 ω L R S hSfin hSne G hGdec ιU hac hmin hdeg3 hinj hint


theorem blf_bk_of_acyclicArmUnion (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), blf_AcyclicArmUnion ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
  apply bgn_bk_of_forest p hp1 hp0
  intro ω L R
  rw [bgn_forest_iff_bc69]
  exact blf_bc69_of_acyclicArmUnion ω L R (hdata ω L R)


end StatMech.Walls
