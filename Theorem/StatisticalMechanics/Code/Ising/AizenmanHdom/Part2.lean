/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean -/

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
import Def.StatisticalMechanics.Code.Ising.AizenmanHdom
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem ahd_triEnds_nd : ∀ i ∈ ({0, 1, 2} : Finset (Fin 3)), ¬ (ahd_triEnds i).IsDiag := by
  decide


theorem ahd_tri_conn_ox : connK ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 1 :=
  Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩


theorem ahd_tri_conn_xy : connK ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 1 2 :=
  Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩


theorem ahd_tri_conn_oy : connK ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 2 :=
  Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩


theorem ahd_tri_allConn :
    aie_allConn ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 1 2 :=
  ⟨ahd_tri_conn_xy, ahd_tri_conn_oy, ahd_tri_conn_ox⟩


theorem ahd_tri_mass_pos :
    (0 : ℝ) < aie_mass ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) (fun _ => 1)
      (sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) := by
  unfold aie_mass
  apply Finset.sum_pos (fun K _ => by norm_num)
  exact ⟨({0, 1, 2} : Finset (Fin 3)), by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, rfl⟩⟩


theorem ahd_hdom_refutable :
    ¬ (2 * (∑ m ∈ ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))).filter
              (fun m => aie_allConn ahd_triEnds m 0 1 2),
            aie_mass ahd_triEnds m (fun _ => 1)
              (sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3))))
        ≤ ∑ m ∈ ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))).filter
              (fun m => aie_noneConn ahd_triEnds m 0 1 2),
            aie_mass ahd_triEnds m (fun _ => 1)
              (sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3)))) := by
  intro hdom
  set m₀ : Finset (Fin 3) := {0, 1, 2} with hm₀
  set A₀ : Finset (Fin 3) := sources ahd_triEnds m₀ with hA₀
  have hall : aie_allConn ahd_triEnds m₀ 0 1 2 := ahd_tri_allConn
  have hnotnone : ¬ aie_noneConn ahd_triEnds m₀ 0 1 2 := by
    rintro ⟨h1, _, _⟩; exact h1 hall.1
  rw [Finset.filter_singleton, if_pos hall, Finset.sum_singleton,
      Finset.filter_singleton, if_neg hnotnone, Finset.sum_empty] at hdom
  have hpos : (0 : ℝ) < aie_mass ahd_triEnds m₀ (fun _ => 1) A₀ := ahd_tri_mass_pos
  linarith


theorem ahd_closure_of_hdom (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
      ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) :
    0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y :=
  aie_inclusion_exclusion ends M hnd A hm hox hoy hxy Φ hΦ hdom


theorem ahd_ghs_distinct_site_of_hdom (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
      ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) :
    (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {x, y}))
      + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, y}))
      + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, x}))
      ≤ ∑ m ∈ M, aie_mass ends m (Φ m) A :=
  aie_ghs_distinct_site ends M hnd A hm hox hoy hxy Φ hΦ hdom

end RandomCurrent
end Sharpness
end StatMech
