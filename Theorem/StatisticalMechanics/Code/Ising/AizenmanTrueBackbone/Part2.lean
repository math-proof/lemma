/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanHdom.Part2
import Def.StatisticalMechanics.Code.Ising.AizenmanTrueBackbone.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

open StatMech.Sharpness.RandomCurrent


local notation "srcK" => StatMech.Sharpness.RandomCurrent.sources

local notation "compK" => StatMech.Sharpness.RandomCurrent.compOf

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem atb_conditionedDom_holds_of_no_allConn (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (A : Finset V) {o x y : V} (Φ : Finset ι → Finset ι → ℝ)
    (hΦnn : ∀ m K, 0 ≤ (Φ m) K)
    (hno : M.filter (fun m => aie_allConn ends m o x y) = ∅) :
    atb_conditionedDom ends M A o x y Φ := by
  unfold atb_conditionedDom
  rw [hno, Finset.sum_empty, mul_zero]
  exact Finset.sum_nonneg (fun m _ => aie_mass_nonneg ends m (Φ m) (hΦnn m) A)


theorem atb_conditioned_closure (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hdom : atb_conditionedDom ends M A o x y Φ) :
    0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y :=
  aie_inclusion_exclusion ends M hnd A hm hox hoy hxy Φ hΦ hdom


theorem atb_tri_x_in_backbone :
    (1 : Fin 3) ∈ atb_backbone ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 :=
  (atb_conn_iff_mem_backbone ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 1).1 ahd_tri_conn_ox


theorem atb_tri_y_in_backbone :
    (2 : Fin 3) ∈ atb_backbone ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 :=
  (atb_conn_iff_mem_backbone ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 2).1 ahd_tri_conn_oy


theorem atb_conditionedDom_refutable :
    ¬ atb_conditionedDom ahd_triEnds ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3)))
        (srcK ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) 0 1 2 (fun _ _ => 1) := by
  unfold atb_conditionedDom
  intro hdom
  set m₀ : Finset (Fin 3) := {0, 1, 2} with hm₀
  set A₀ : Finset (Fin 3) := srcK ahd_triEnds m₀ with hA₀
  
  have hall : aie_allConn ahd_triEnds m₀ 0 1 2 :=
    (atb_allConn_iff_xy_in_backbone ahd_triEnds m₀ 0 1 2).2
      ⟨atb_tri_x_in_backbone, atb_tri_y_in_backbone⟩
  have hnotnone : ¬ aie_noneConn ahd_triEnds m₀ 0 1 2 := by
    rintro ⟨h1, _, _⟩; exact h1 hall.1
  rw [Finset.filter_singleton, if_pos hall, Finset.sum_singleton,
      Finset.filter_singleton, if_neg hnotnone, Finset.sum_empty] at hdom
  have hpos : (0 : ℝ) < aie_mass ahd_triEnds m₀ (fun _ => 1) A₀ := ahd_tri_mass_pos
  linarith

end Ising
end StatMech
