/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.BoxFeketeData.Part2
import Def.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false


namespace StatMech

namespace FK

variable {d : ℕ}


theorem fis_boxInterfaceData_of_split (t : ℝ) (hsplit : fis_UniformBoxSplit d t) :
    bfd_FKInterfaceData d t := by
  obtain ⟨C, κ, hC, hκ, hglue, hbdd, he⟩ := hsplit
  exact fis_interfaceData_of_bounded (boxGraph d ·) 2 t C hC hglue hbdd κ hκ he


theorem fis_gluingBound_of_crossSplit (t : ℝ) (m n : ℕ)
    (K : SimpleGraph (boxVerts d m ⊕ boxVerts d n)) [DecidableRel K.Adj]
    (hci : fis_CrossInterface (boxGraph d m) (boxGraph d n) K)
    (φ : boxGraph d (m + n) ≃g K) :
    - Real.log (fkZ (boxGraph d (m + n)) (fsc_logistic t) 2)
      ≤ - Real.log (fkZ (boxGraph d m) (fsc_logistic t) 2)
        + - Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2)
        + (fis_interface (boxGraph d m) (boxGraph d n) K).card
            * (- Real.log (1 - fsc_logistic t)) := by
  set p := fsc_logistic t with hp
  have hp0 : (0:ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  have hiso : fkZ (boxGraph d (m + n)) p 2 = fkZ K p 2 := fsm_fkZ_iso _ K φ p 2
  have hint := fis_neglog_interface_le hci hp0 hp1 (by norm_num : (0:ℝ) < 2)
  rw [hiso]
  have hrw : (fis_interface (boxGraph d m) (boxGraph d n) K).card * (- Real.log (1 - p))
      = - ((fis_interface (boxGraph d m) (boxGraph d n) K).card * Real.log (1 - p)) := by ring
  rw [hrw]
  linarith [hint]


theorem fis_fk_uniqueness_of_boxSplit (hd : 1 ≤ d) (N : ℕ)
    (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hsplit : ∀ t, fis_UniformBoxSplit d t)
    (hfreeBulk : ubd_FreeUniformBulkDeviation (d := d) N)
    (hwiredBulk : ubd_WiredUniformBulkDeviation (d := d) N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  bfd_fk_uniqueness_of_interface_and_uniformBulk hd N eb hEbox
    (fun t => fis_boxInterfaceData_of_split t (hsplit t)) hfreeBulk hwiredBulk


theorem fis_boundedGluing_satisfiable :
    ∃ (u : ℕ → ℝ) (e : ℕ → ℝ) (C κ : ℝ), 0 ≤ C ∧ κ ≠ 0 ∧
      (∀ m n, u (m + n) ≤ u m + u n + C)
      ∧ BddBelow (Set.range fun n => (u n + C) / n)
      ∧ Tendsto (fun n => e n / n) atTop (𝓝 κ) := by
  refine ⟨fun _ => 0, fun n => (n : ℝ), 0, 1, le_refl 0, one_ne_zero, ?_, ?_, ?_⟩
  · intro m n; simp
  · exact ⟨0, by rintro x ⟨n, rfl⟩; simp⟩
  · refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1:ℝ)))
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp


theorem fis_crossInterface_satisfiable {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] :
    fis_CrossInterface (⊥ : SimpleGraph V) (⊥ : SimpleGraph W)
      (⊥ : SimpleGraph (V ⊕ W)) := by
  refine ⟨?_, ?_, ?_⟩
  · 
    intro x y hxy
    match x, y, hxy with
    | Sum.inl a, Sum.inl b, hxy => simp only [SimpleGraph.sum_adj, SimpleGraph.bot_adj] at hxy
    | Sum.inr c, Sum.inr d, hxy => simp only [SimpleGraph.sum_adj, SimpleGraph.bot_adj] at hxy
    | Sum.inl a, Sum.inr d, hxy => simp only [SimpleGraph.sum_adj] at hxy
    | Sum.inr c, Sum.inl b, hxy => simp only [SimpleGraph.sum_adj] at hxy
  · intro a b h; exact absurd h (by simp)
  · intro c d h; exact absurd h (by simp)

end FK
end StatMech
