/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgtgenuineforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.btrtrifnotion.Part3
import Def.StatisticalMechanics.Code.Walls.bgtgenuineforest
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


theorem bgt_genuineTcount_le_leafCard (ω : ConfigSpace (Sym2 (Site d))) (L R m : ℕ)
    (h : bgt_GenuineForestNoBnd ω L R m) :
    (btr_genuineTrifFinset ω L R).card ≤ m := by
  classical
  obtain ⟨W, _, hne, _, G, _, ιT, hacyc, hmin, hdeg3, hιinj, hleaf⟩ := h
  haveI := hne
  set Tf := btr_genuineTrifFinset ω L R with hTf
  set Tw : Finset W := Tf.image ιT with hTw
  have hιinjOn : Set.InjOn ιT Tf := by
    intro y hy z hz hyz
    rw [Finset.mem_coe, bgt_mem_genuineTrifFinset] at hy hz
    exact hιinj y hy.1 hy.2 z hz.1 hz.2 hyz
  have hcardTw : Tw.card = Tf.card := by rw [hTw, Finset.card_image_of_injOn hιinjOn]
  have hTwdeg : ∀ w ∈ Tw, 3 ≤ G.degree w := by
    intro w hw
    rw [hTw, Finset.mem_image] at hw
    obtain ⟨y, hyT, rfl⟩ := hw
    rw [bgt_mem_genuineTrifFinset] at hyT
    exact hdeg3 y hyT.1 hyT.2
  calc (btr_genuineTrifFinset ω L R).card = Tf.card := rfl
    _ = Tw.card := hcardTw.symm
    _ ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := flc2_trifImage_card_le_deg3 G Tw hTwdeg
    _ ≤ (univ.filter (fun v => G.degree v = 1)).card := flc2_forest_internal_le_leaves G hacyc hmin
    _ ≤ m := hleaf


end StatMech.Walls
