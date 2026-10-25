/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc31surgery.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc32surgery
import Theorem.StatisticalMechanics.Code.Ising.BackboneResummation.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.HdomMultiplicity.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Def.StatisticalMechanics.Code.Walls.gc33witness.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc33_massDoubling_of_sourceClusterResummation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V)
    (h : gc33_SourceClusterResummation G β J M B o x y) :
    gc31_MassDoublingSurgery G β J M B o x y := by
  obtain ⟨μ, Ψ, hμpos, hμle, hmem, hinj, hbound⟩ := h
  refine ⟨Ψ, hmem, hinj, fun m hm => ?_⟩
  have hb := hbound m hm
  have hnn : 0 ≤ hnw_mass G β J (Ψ m) B := hnw_mass_nonneg G β J hβ hJ (Ψ m) B
  have : μ * hnw_mass G β J (Ψ m) B ≤ hnw_mass G β J (Ψ m) B := by nlinarith
  linarith


theorem gc33_B_status {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V) :
    (gc33_SourceClusterResummation G β J M B o x y
        → gc31_MassDoublingSurgery G β J M B o x y)
      ∧ (∀ (ma : Sharpness.Current V), ma ∈ bbr_allFilter G M o x y →
          0 < hnw_mass G β J ma B →
          (∀ m' ∈ bbr_noneFilter G M o x y, hnw_mass G β J m' B = 0) →
          ¬ gc31_MassDoublingSurgery G β J M B o x y) := by
  refine ⟨gc33_massDoubling_of_sourceClusterResummation G β J hβ hJ M B o x y, ?_⟩
  intro ma hma hpos hzero
  exact gc33_surgery_unsat_of_zero_targets G β J hβ hJ M B o x y ma hma hpos hzero

end StatMech.Walls
