/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bscsupercut.Part2
import Theorem.StatisticalMechanics.Code.Walls.bfcfaithful
import Theorem.StatisticalMechanics.Code.Walls.bgnglobalcontract.Part4
import Def.StatisticalMechanics.Code.Walls.baoallopen
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

theorem bao_allOpenTrif_imp_bc67 {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ}
    (h : bao_AllOpenTrif ω L) : bc67_IsGnTrifurcation ω L (0 : Site 2) :=
  h.1


theorem bao_box_internallyConnected {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ}
    (h : bao_AllOpenTrif ω L) {x y : Site 2}
    (hx : x ∈ Lattice.box 2 L) (hy : y ∈ Lattice.box 2 L) :
    Lattice.Connected 2 ω x y :=
  bff_allOpen_box_connected h.2 hx hy

#check @bao_AllOpenTrif
#check @bao_allOpenTrif_imp_bc67
#check @bao_box_internallyConnected


theorem bao_boxEdges_fst {n : ℕ} {x y : Site 2} (h : s(x, y) ∈ boxEdges 2 n) :
    x ∈ Lattice.box 2 n := by
  simp only [boxEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    boxFinsetBK, Set.Finite.mem_toFinset] at h
  obtain ⟨p, ⟨⟨hp1, hp2⟩, _⟩, hpe⟩ := h
  rw [Sym2.eq_iff] at hpe
  rcases hpe with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1]; exact hp1
  · rw [← h2]; exact hp2


end StatMech.Walls
