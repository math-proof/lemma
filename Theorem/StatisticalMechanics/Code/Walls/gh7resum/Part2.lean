/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh7resum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gh6attach
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc82grahamgeometric.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Def.StatisticalMechanics.Code.Walls.gh7resum
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gh7_perSuperposition_count_nonpos_of_eq22 {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (heq22 : gh7_perSuperposition_eq22 ends m o x y g) :
    (gc85b_threeGapCount ends m o x y g : ℝ) ≤ 0 := by
  obtain ⟨surv, V₁, V₂, V₁', V₂', wgtA, diffA, wgtB, diffB,
    hwgtA, hdiffA, hwgtB, hdiffB, hident, hsurv⟩ := heq22
  have hA : 0 ≤ (∑ A ∈ m.powerset, (gh4_compMass ends m V₁ V₂ o A : ℝ) * wgtA A * diffA A) :=
    gh4_drop_nonneg ends m V₁ V₂ o wgtA diffA hwgtA hdiffA
  have hB : 0 ≤ (∑ B ∈ m.powerset, (gh4_compMass ends m V₁' V₂' o B : ℝ) * wgtB B * diffB B) :=
    gh4_drop_nonneg ends m V₁' V₂' o wgtB diffB hwgtB hdiffB
  rw [hident]; linarith


theorem gh7_ghs_of_perSuperposition_eq22 (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (heq22 : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
        sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
        gh7_perSuperposition_eq22 (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  apply gc85b_ursell_nonpos_of_bijection G β h hβ hh o x y hox hoy hxy _ hsupp
  intro m hm
  
  rw [← gc85b_threeGapCount_nonpos_iff_bijection]
  have hcount : (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ)
      ≤ 0 := gh7_perSuperposition_count_nonpos_of_eq22 _ _ _ _ _ _ (heq22 m hm)
  exact_mod_cast hcount


theorem gh7_status : True := trivial

end StatMech.Walls
