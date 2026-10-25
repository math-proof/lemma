/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem stac_removeSites_no_neighbor (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {x w : Site d} (hxT : x ∈ T) : ¬ (openSubgraph d (removeSites T ω)).Adj x w := by
  intro hadj
  have : (removeSites T ω) s(x, w) = true := hadj.2
  rw [removeSites, if_pos ⟨x, hxT, Sym2.mem_mk_left x _⟩] at this
  exact Bool.false_ne_true this


theorem stac_removeSites_connected_eq (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {x v : Site d} (hxT : x ∈ T) (hconn : Connected d (removeSites T ω) x v) : v = x := by
  rcases hconn with ⟨w⟩
  cases w with
  | nil => rfl
  | cons hadj p => exact absurd hadj (stac_removeSites_no_neighbor T ω hxT)


theorem stac_removeSites_cluster_singleton (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {x : Site d} (hxT : x ∈ T) :
    cluster d (removeSites T ω) x = {x} := by
  ext v
  simp only [mem_cluster, Set.mem_singleton_iff]
  exact ⟨fun h => stac_removeSites_connected_eq T ω hxT h, fun h => h ▸ connected_rfl⟩


theorem stac_infiniteCluster_notMem (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {w : Site d} (hinf : (cluster d (removeSites T ω) w).Infinite) : w ∉ T := by
  intro hwT
  rw [stac_removeSites_cluster_singleton T ω hwT] at hinf
  exact hinf (Set.finite_singleton w)


theorem stac_sameArm_of_sameClass (ω : ConfigSpace (Sym2 (Site d))) {x₀ aj u v : Site d}
    (hxu : Connected d ω x₀ u) (hneu : x₀ ≠ u)
    (hxv : Connected d ω x₀ v) (hnev : x₀ ≠ v)
    (hu : Connected d (removeSite x₀ ω) aj u)
    (hv : Connected d (removeSite x₀ ω) aj v) :
    fsp_sameArm ω x₀ u v := by
  unfold fsp_sameArm
  have hwu := fsp_armWitness_inArm ω hxu hneu
  have hwv := fsp_armWitness_inArm ω hxv hnev
  exact hwu.trans (hu.symm.trans (hv.trans hwv.symm))


theorem stac_claw_unsat
    (cx : Fin 3) (cy : Fin 3 → Fin 3)
    (ay : Fin 3 → Fin 3) (ayj : Fin 3 → Fin 3 → Fin 3)
    (Gay : ∀ i, ay i = 0 ↔ cy i ≠ i)
    (Gayj : ∀ i j, ayj i j = 0 ↔ cy j ≠ i)
    (Dx0 : ∀ i, cx ≠ cy i)
    (Dyiyj : ∀ i j, j ≠ i → ay i ≠ ayj i j) :
    False := by
  
  have step1 : ∀ i j : Fin 3, j ≠ i → cy i = i ∨ cy j = i := by
    intro i j hji
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hi, hj⟩ := hcon
    have h1 : ay i = 0 := (Gay i).mpr hi
    have h2 : ayj i j = 0 := (Gayj i j).mpr hj
    exact Dyiyj i j hji (by rw [h1, h2])
  
  have step2 : ∀ a : Fin 3, cy a = a := by
    intro a
    by_contra ha
    have hall : ∀ j : Fin 3, j ≠ a → cy j = a := by
      intro j hj
      rcases step1 a j hj with h | h
      · exact absurd h ha
      · exact h
    obtain ⟨b, c, hb, hc, hbc⟩ : ∃ b c : Fin 3, b ≠ a ∧ c ≠ a ∧ c ≠ b := by
      fin_cases a
      · exact ⟨1, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 1, by decide, by decide, by decide⟩
    have hcyb : cy b = a := hall b hb
    have hcyc : cy c = a := hall c hc
    rcases step1 b c hbc with h | h
    · exact hb ((hcyb.symm.trans h).symm)
    · exact hb ((hcyc.symm.trans h).symm)
  
  exact Dx0 cx (by rw [step2 cx])


theorem stac_claw_shadow_consistent :
    ∃ (cy : Fin 3 → Fin 3) (ay : Fin 3 → Fin 3) (ayj : Fin 3 → Fin 3 → Fin 3),
      (∀ i, ay i = 0 ↔ cy i ≠ i) ∧ (∀ i j, ayj i j = 0 ↔ cy j ≠ i) := by
  classical
  refine ⟨id, fun _ => 1, fun i j => if j = i then 1 else 0, ?_, ?_⟩
  · intro i
    have hl : ¬ ((1 : Fin 3) = 0) := by decide
    have hr : ¬ (id i ≠ i) := fun h => h rfl
    exact ⟨fun h => absurd h hl, fun h => absurd h hr⟩
  · intro i j
    show (if j = i then (1 : Fin 3) else 0) = 0 ↔ id j ≠ i
    by_cases hji : j = i
    · have hl : ¬ ((1 : Fin 3) = 0) := by decide
      have hr : ¬ (id j ≠ i) := by rw [id_eq, hji]; exact fun h => h rfl
      rw [if_pos hji]
      exact ⟨fun h => absurd h hl, fun h => absurd h hr⟩
    · rw [if_neg hji]
      exact ⟨fun _ => fun h => hji h, fun _ => rfl⟩


end Percolation
end StatMech
