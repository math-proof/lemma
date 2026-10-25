/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.blfboundaryleaf.Part3
import Def.StatisticalMechanics.Code.Walls.bauacyclicarm
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


theorem bau_blf_of_subforestData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) : blf_AcyclicArmUnion ω L R := by
  obtain ⟨S, hSfin, hSne, H, T, G, hGdec, ιU, hHconn, hTH, hT, hle, hmin, hdeg3, hinj, hint⟩ := h
  exact ⟨S, hSfin, hSne, G, hGdec, ιU, bau_isAcyclic_of_le_tree hT hle, hmin, hdeg3, hinj, hint⟩


theorem bau_bc69_of_subforestData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) : bc69_Gn_globalForest ω L R :=
  blf_bc69_of_acyclicArmUnion ω L R (bau_blf_of_subforestData ω L R h)


theorem bau_bk_of_subforestData (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
  apply blf_bk_of_acyclicArmUnion p hp1 hp0
  intro ω L R
  exact bau_blf_of_subforestData ω L R (hdata ω L R)


end StatMech.Walls
