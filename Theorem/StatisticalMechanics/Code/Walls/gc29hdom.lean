/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc28ghsrigid
import Theorem.StatisticalMechanics.Code.Ising.TwoCurrentProbBound
import Theorem.StatisticalMechanics.Code.Ising.CrossClassHdom
import Theorem.StatisticalMechanics.Code.Ising.HdomMultiplicity.Part2
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
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc29_allConnMass_le_partitionFunction (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V) :
    (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B)
      ≤ ∑ m ∈ M, hnw_mass G β J m B :=
  tcp_allConnMass_le_partitionFunction G β J hβ hJ M B o x y


theorem gc29_allConn_prob_le_one (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnProb G β J M B o x y ≤ 1 :=
  tcp_allConn_prob_le_one G β J hβ hJ M B o x y


theorem gc29_allConnMass_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V) :
    0 ≤ ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B :=
  tcp_allConnMass_nonneg G β J hβ hJ M B o x y


theorem gc29_hdom_iff_full_gap_nonneg (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Sharpness.Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = B) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
    (2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B)
        ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m B)
      ↔ 0 ≤ ∑ m ∈ M, hnw_gap G β J m B o x y :=
  cch_crossClass_dom_iff_le G β J M hnd B hm hox hoy hxy hcoh


theorem gc29_full_gap_can_be_negative :
    ∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))),
        hnw_gap hmu_TriG 1 (fun _ => 1) m ∅ 0 1 2 < 0 :=
  cch_full_gap_can_be_negative


theorem gc29_triangle_probLeOne :
    (∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))).filter
        (fun m => hnw_allConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅)
      ≤ ∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅ :=
  gc29_allConnMass_le_partitionFunction hmu_TriG 1 (fun _ => 1) (by norm_num)
    (fun _ => by norm_num) {hmu_triM} ∅ 0 1 2


theorem gc29_probLeOne_does_not_give_hdom :
    
    ((∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))).filter
        (fun m => hnw_allConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅)
      ≤ ∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅)
    
    ∧ ¬ (2 * (∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))).filter
            (fun m => hnw_allConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅)
        ≤ ∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))).filter
            (fun m => hnw_noneConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) :=
  ⟨gc29_triangle_probLeOne, hmu_hdom_refutable⟩


theorem gc29_allConn_summed_gap_eq (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Sharpness.Current V)) (B : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y
      = -2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B) := by
  have := tcp_lebowitz_summed_gap G β J M B hox hoy hxy
  unfold tcp_allConnMass at this
  exact this


theorem gc29_full_gap_eq_allConn_gap_add_noneMass (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Sharpness.Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = B) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
    ∑ m ∈ M, hnw_gap G β J m B o x y
      = (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y)
        + ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m B := by
  rw [hnw_inclusion_exclusion_decomp G β J M hnd B hm hox hoy hxy hcoh,
      gc29_allConn_summed_gap_eq G β J M B hox hoy hxy]
  ring


end StatMech.Walls
