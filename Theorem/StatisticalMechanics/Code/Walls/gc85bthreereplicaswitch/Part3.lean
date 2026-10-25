/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc83crosspairing.Part3
import Def.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
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

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap


variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


open StatMech.Sharpness.FluxEdgeCopy


theorem gc85b_threeGapCount_nonpos_of_bijection (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (hbij : gc85b_ThreeCurrentBijection ends m o x y g) :
    gc85b_threeGapCount ends m o x y g ≤ 0 := by
  unfold gc85b_threeGapCount gc85b_ThreeCurrentBijection at *
  omega


theorem gc85b_threeGapCount_nonpos_iff_bijection (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc85b_threeGapCount ends m o x y g ≤ 0 ↔ gc85b_ThreeCurrentBijection ends m o x y g := by
  unfold gc85b_threeGapCount gc85b_ThreeCurrentBijection
  omega


theorem gc85b_pairwise_insufficient :
    ∃ c00 c0og c0ox c0oy cogxg : ℤ,
      0 ≤ c00 ∧ 0 ≤ c0og ∧ 0 ≤ c0ox ∧ 0 ≤ c0oy ∧ 0 ≤ cogxg
      ∧ cogxg ≤ c0og ∧ cogxg ≤ c0ox ∧ cogxg ≤ c0oy ∧ cogxg ≤ c00
      ∧ ¬ (c00 + 2 * cogxg ≤ c0og + c0ox + c0oy) := by
  refine ⟨4, 1, 1, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc85b_gc15_threeGap_eq_count (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (m : ↥(withGhost G).edgeFinset → ℕ)
    (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V))) :
    gc15_threeGap G β h o x y m
      = (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ)
        * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ)) with hJ'
  set w := weight (withGhost G) β J' (ofEdgeFun (withGhost G) m) with hw
  
  unfold gc15_threeGap gc15_tFiber gc85b_threeGapCount
  rw [gc15_sd0 (some o) (some x) (some y) none,
      gc15_sd1 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd2 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd3 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd4 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg]
  rw [if_pos hm, if_pos hm, if_pos hm, if_pos hm, if_pos hm]
  
  rw [gc85b_tpsum_eq_pcount (withGhost G) β J' m ∅ ∅,
      gc85b_tpsum_eq_pcount (withGhost G) β J' m ∅ {some o, none},
      gc85b_tpsum_eq_pcount (withGhost G) β J' m ∅ {some o, some x},
      gc85b_tpsum_eq_pcount (withGhost G) β J' m ∅ {some o, some y},
      gc85b_tpsum_eq_pcount (withGhost G) β J' m {some o, none} {some x, none}]
  push_cast
  ring


theorem gc85b_gc15_threeGap_nonpos_of_bijection (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (m : ↥(withGhost G).edgeFinset → ℕ)
    (hbij : sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
        gc85b_ThreeCurrentBijection (endsM (withGhost G) m) univ (some o) (some x) (some y) none) :
    gc15_threeGap G β h o x y m ≤ 0 := by
  by_cases hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
      = ({some o, some x, some y, none} : Finset (Option V))
  · rw [gc85b_gc15_threeGap_eq_count G β h o x y hox hoy hxy m hm]
    have hcount : gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none ≤ 0 :=
      gc85b_threeGapCount_nonpos_of_bijection _ _ _ _ _ _ (hbij hm)
    have hwt : 0 ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) :=
      gc83_weight_nonneg G β h hβ hh _
    have : (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ) ≤ 0 := by
      exact_mod_cast hcount
    nlinarith [this, hwt]
  · exact le_of_eq (gc15_threeGap_vanish G β h o x y hox hoy hxy m hm)


theorem gc85b_ursell_nonpos_of_bijection (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbij : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
        sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
        gc85b_ThreeCurrentBijection (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  have hsign : gc82_ThreeGapNonpos G β h o x y := fun m =>
    gc85b_gc15_threeGap_nonpos_of_bijection G β h hβ hh o x y hox hoy hxy m (hbij m)
  exact gc82_ursell_nonpos G β h o x y hox hoy hxy hsign hsupp


theorem gc85b_three_replica_status (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    
    (∀ m : ↥(withGhost G).edgeFinset → ℕ,
        sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
        gc15_threeGap G β h o x y m
          = (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ)
            * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m))
    
    ∧ (∃ c00 c0og c0ox c0oy cogxg : ℤ,
        0 ≤ c00 ∧ 0 ≤ c0og ∧ 0 ≤ c0ox ∧ 0 ≤ c0oy ∧ 0 ≤ cogxg
        ∧ cogxg ≤ c0og ∧ cogxg ≤ c0ox ∧ cogxg ≤ c0oy ∧ cogxg ≤ c00
        ∧ ¬ (c00 + 2 * cogxg ≤ c0og + c0ox + c0oy))
    
    ∧ ((∀ m : ↥(withGhost G).edgeFinset → ℕ,
          sources (withGhost G) (ofEdgeFun (withGhost G) m)
            = ({some o, some x, some y, none} : Finset (Option V)) →
          gc85b_ThreeCurrentBijection (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
        → gc82_ThreeGapAllConnSupported G β h o x y
        → eg_ursell3 G β h o x y ≤ 0) :=
  ⟨fun m hm => gc85b_gc15_threeGap_eq_count G β h o x y hox hoy hxy m hm,
   gc85b_pairwise_insufficient,
   fun hbij hsupp => gc85b_ursell_nonpos_of_bijection G β h hβ hh o x y hox hoy hxy hbij hsupp⟩

end StatMech.Walls
