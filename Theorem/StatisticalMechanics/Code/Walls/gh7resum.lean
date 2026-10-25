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


theorem gh7_sumA_is_per_superposition {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W) :
    gc85b_pcount ends m V₁ V₂ = ∑ A ∈ m.powerset, gh4_compMass ends m V₁ V₂ u A :=
  gh4_compMass_partition ends m V₁ V₂ u


theorem gh7_threeGapCount_component_decomp {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc85b_threeGapCount ends m o x y g
      = ∑ A ∈ m.powerset,
          ((gh4_compMass ends m ∅ ∅ o A : ℤ)
            - (gh4_compMass ends m ∅ {o, g} o A : ℤ)
            - (gh4_compMass ends m ∅ {o, x} o A : ℤ)
            - (gh4_compMass ends m ∅ {o, y} o A : ℤ)
            + 2 * (gh4_compMass ends m {o, g} {x, g} o A : ℤ)) := by
  unfold gc85b_threeGapCount
  rw [gh4_compMass_partition ends m ∅ ∅ o,
      gh4_compMass_partition ends m ∅ {o, g} o,
      gh4_compMass_partition ends m ∅ {o, x} o,
      gh4_compMass_partition ends m ∅ {o, y} o,
      gh4_compMass_partition ends m {o, g} {x, g} o]
  push_cast
  rw [Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, Finset.mul_sum]


theorem gh7_resummation_assembly (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hsign : ∀ m : ↥(withGhost G).edgeFinset → ℕ, gc15_threeGap G β h o x y m ≤ 0) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc15_ursell_nonpos_of_perConfig G β h o x y hox hoy hxy hsign


theorem gh7_ghs_of_perSuperposition_count (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbij : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
        sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
        gc85b_ThreeCurrentBijection (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc85b_ursell_nonpos_of_bijection G β h hβ hh o x y hox hoy hxy hbij hsupp


theorem gh7_perSuperposition_drop_nonneg {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W)
    (wgt diff : Finset ι → ℝ) (hwgt : ∀ A, 0 ≤ wgt A) (hdiff : ∀ A, 0 ≤ diff A) :
    0 ≤ ∑ A ∈ m.powerset, (gh4_compMass ends m V₁ V₂ u A : ℝ) * wgt A * diff A :=
  gh4_drop_nonneg ends m V₁ V₂ u wgt diff hwgt hdiff


end StatMech.Walls
