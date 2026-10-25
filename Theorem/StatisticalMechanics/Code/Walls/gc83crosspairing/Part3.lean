/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc83crosspairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc82grahamgeometric.Part2
import Abbrev.StatisticalMechanics.Code.Walls.gc83crosspairing
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

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc83_ursell_nonpos_of_missingBijection (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbij : gc83_MissingBijection G β h o x y)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc83_ursell_nonpos_of_netNonpos G β h o x y hox hoy hxy hbij hsupp


theorem gc83_crosspairing_status (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (∀ m : ↥(withGhost G).edgeFinset → ℕ,
        gc15_threeGap G β h o x y m
          = (if gc83_fourMark G o x y m
              then gc83_fam1 G β h o x y m + 2 * gc83_fam2 G β h o x y m else 0))
    ∧ (∀ m : ↥(withGhost G).edgeFinset → ℕ, 0 ≤ gc83_fam2 G β h o x y m)
    ∧ (gc83_NetNonpos G β h o x y ↔ gc82_ThreeGapNonpos G β h o x y) :=
  ⟨fun m => gc83_threeGap_eq_fam G β h o x y hox hoy hxy m,
   fun m => gc83_fam2_nonneg G β h hβ hh o x y m,
   gc83_netNonpos_iff_threeGapNonpos G β h o x y hox hoy hxy⟩

end StatMech.Walls
