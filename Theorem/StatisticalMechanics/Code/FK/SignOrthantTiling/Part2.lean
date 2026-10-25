/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Instance.StatisticalMechanics.Code.FK.SignOrthantTiling.Part2
open MeasureTheory Set Filter Topology Real
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


theorem sot_fkZ_bot_pempty {p q : ℝ} : fkZ (⊥ : SimpleGraph PEmpty) p q = 1 := by
  unfold fkZ
  rw [Finset.sum_eq_single (fun (_ : Sym2 PEmpty) => false)]
  · unfold fkWeight edgeProduct numClusters
    rw [Finset.prod_of_isEmpty, one_mul]
    rw [show Fintype.card (openSub (⊥ : SimpleGraph PEmpty) (fun _ => false)).ConnectedComponent = 0
        from by
          rw [Fintype.card_eq_zero_iff]
          exact ⟨fun c => c.recOnSubsingleton (fun x => x.elim)⟩,
      pow_zero]
  · intro b _ hb
    exact absurd (Subsingleton.elim b _) hb
  · intro h; exact absurd (Finset.mem_univ _) h


theorem sot_repGraph_Z_ge (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∀ k, (fkZ G p q) ^ k ≤ fkZ (sot_repGraph V G k) p q := by
  intro k
  induction k with
  | zero =>
    rw [pow_zero]
    
    have : fkZ (sot_repGraph V G 0) p q = 1 := sot_fkZ_bot_pempty
    rw [this]
  | succ k ih =>
    rw [pow_succ]
    
    
    have hsucc : fkZ (sot_repGraph V G (k + 1)) p q = fkZ (G ⊕g sot_repGraph V G k) p q := by
      congr 1
    rw [hsucc]
    calc (fkZ G p q) ^ k * fkZ G p q
        ≤ fkZ (sot_repGraph V G k) p q * fkZ G p q :=
          mul_le_mul_of_nonneg_right ih (fkZ_pos G hp hp1 hq).le
      _ = fkZ G p q * fkZ (sot_repGraph V G k) p q := by ring
      _ ≤ fkZ (G ⊕g sot_repGraph V G k) p q := fsm_fkZ_sum_ge G (sot_repGraph V G k) hp hp1 hq


theorem sot_edge_card_lower (d n : ℕ) (hd : 1 ≤ d) :
    (n : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1) ≤ ((boxGraph d n).edgeFinset.card : ℝ) := by
  have h1 := boxSV_edge_card_lower (d := d) (n := n) hd
  rw [fup_edge_card_eq d n] at h1
  have hnat : n * (2 * n + 1) ^ (d - 1) ≤ (boxGraph d n).edgeFinset.card := by
    have h2 : 2 * (n * (2 * n + 1) ^ (d - 1)) ≤ 2 * (boxGraph d n).edgeFinset.card := by
      rw [show 2 * (n * (2 * n + 1) ^ (d - 1)) = (2 * n) * (2 * n + 1) ^ (d - 1) by ring]
      exact h1
    omega
  calc (n : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1) = ((n * (2 * n + 1) ^ (d - 1) : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hnat


theorem sot_summable_of_surfaceBound (d : ℕ) (hd : 1 ≤ d) (C : ℝ) (hC : 0 ≤ C)
    (I : ℕ → ℝ) (hI0 : ∀ j, 0 ≤ I j)
    (hIB : ∀ j, I j ≤ C * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)) :
    Summable (fun j => I j / bxt_E d (2 ^ (j + 1))) := by
  
  refine Summable.of_nonneg_of_le (f := fun j => (C / 2) * (1 / 2 : ℝ) ^ j)
    (fun j => div_nonneg (hI0 j) (bxt_E_nonneg d _)) ?_ ?_
  · intro j
    
    have hedge : (2 * (2 : ℝ) ^ j) * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1) ≤ bxt_E d (2 ^ (j + 1)) := by
      have h := sot_edge_card_lower d (2 ^ (j + 1)) hd
      have hpow : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ j := by push_cast; ring
      rw [bxt_E]
      calc (2 * (2 : ℝ) ^ j) * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)
          = ((2 ^ (j + 1) : ℕ) : ℝ) * (2 * ((2 ^ (j + 1) : ℕ) : ℝ) + 1) ^ (d - 1) := by
            rw [hpow]; ring_nf
        _ ≤ ((boxGraph d (2 ^ (j + 1))).edgeFinset.card : ℝ) := h
    
    have hpow_pos : (0 : ℝ) < (4 * (2 : ℝ) ^ j + 1) ^ (d - 1) := by positivity
    have hden_pos : (0 : ℝ) < (2 * (2 : ℝ) ^ j) * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1) := by positivity
    calc I j / bxt_E d (2 ^ (j + 1))
        ≤ I j / ((2 * (2 : ℝ) ^ j) * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)) :=
          div_le_div_of_nonneg_left (hI0 j) hden_pos hedge
      _ ≤ (C * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)) /
            ((2 * (2 : ℝ) ^ j) * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)) :=
          div_le_div_of_nonneg_right (hIB j) hden_pos.le
      _ = (C / 2) * (1 / 2 : ℝ) ^ j := by
          have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
          rw [div_pow, one_pow]
          field_simp
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (C / 2)


end FK
end StatMech
