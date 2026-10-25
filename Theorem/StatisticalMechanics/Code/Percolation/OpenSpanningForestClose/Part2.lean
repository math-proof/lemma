/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoundaryPruningClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKSpanningTreeClose.Part2
import Def.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem osf_boxOpenForest_of_peeled (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : osf_PeeledBoxForest ω n) : bst_BoxOpenForest ω n := by
  classical
  obtain ⟨Vset, hVne, F₀, vx, b, hπ0, hmin, htriData, hleaf⟩ := h
  refine ⟨Vset, hVne, osf_spanForest F₀, Classical.decRel _, vx, b, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro u v huv
    exact hπ0 u v (osf_spanForest_le F₀ huv)
  · 
    exact osf_spanForest_acyclic F₀
  · 
    exact hmin
  · 
    intro x hxbox htri
    obtain ⟨hvx, hreach, hcut⟩ := htriData x hxbox htri
    refine ⟨hvx, ?_, hcut⟩
    intro i
    obtain ⟨hr, hne⟩ := hreach i
    exact ⟨osf_spanForest_reachable_of F₀ hr, hne⟩
  · 
    exact hleaf


open Classical in


theorem osf_peeledBoxForest_of_acyclic (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (Vset : Finset (Site d)) (hVne : Nonempty (↑Vset : Type)) (F₀ : SimpleGraph (↑Vset : Type))
    [DecidableRel F₀.Adj] (hac : F₀.IsAcyclic)
    (vx : Site d → (↑Vset : Type)) (b : Site d → Fin 3 → (↑Vset : Type))
    (hπ0 : ∀ u v, F₀.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d))
    (hmin : ∀ v : (↑Vset : Type), 1 ≤ F₀.degree v)
    (htriData : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ((vx x : Site d) = x ∧
       (∀ i, F₀.Reachable (vx x) (b x i) ∧ b x i ≠ vx x) ∧
       (¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d))))
    (hleaf : ∀ v : (↑Vset : Type), F₀.degree v = 1 → (v : Site d) ∈ vertexBoundary d n) :
    osf_PeeledBoxForest ω n := by
  classical
  refine ⟨Vset, hVne, F₀, vx, b, hπ0, ?_, htriData, ?_⟩
  · intro v
    rw [osf_spanForest_degree_of_acyclic F₀ hac]
    exact hmin v
  · intro v hv
    rw [osf_spanForest_degree_of_acyclic F₀ hac] at hv
    exact hleaf v hv


open Classical in


theorem osf_peeledBoxForest_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
            ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
            ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
    osf_PeeledBoxForest ω n := by
  classical
  
  set lab : Fin 4 → Site d := fun v => match v with
    | 0 => x | 1 => a 0 | 2 => a 1 | 3 => a 2 with hlab
  have hlabinj : Function.Injective lab := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp only [hlab] at huv <;>
      first
        | rfl
        | (exact absurd huv (hxne 0).symm) | (exact absurd huv (hxne 1).symm)
        | (exact absurd huv (hxne 2).symm) | (exact absurd huv.symm (hxne 0).symm)
        | (exact absurd huv.symm (hxne 1).symm) | (exact absurd huv.symm (hxne 2).symm)
        | (exact absurd (hainj huv) (by decide))
  set Vset : Finset (Site d) := Finset.univ.image lab with hVset
  have hmem : ∀ i : Fin 4, lab i ∈ Vset := fun i => by
    rw [hVset, Finset.mem_image]; exact ⟨i, Finset.mem_univ _, rfl⟩
  set e : Fin 4 ≃ (↑Vset : Type) :=
    Equiv.ofBijective (fun i => (⟨lab i, hmem i⟩ : (↑Vset : Type)))
      ⟨fun u v huv => hlabinj (Subtype.ext_iff.mp huv),
        fun ⟨y, hy⟩ => by
          rw [hVset, Finset.mem_image] at hy
          obtain ⟨i, _, rfl⟩ := hy
          exact ⟨i, rfl⟩⟩ with he
  have heval : ∀ i, (e i : Site d) = lab i := fun i => rfl
  
  let F₀ : SimpleGraph (↑Vset : Type) := Flc2Witness.starG.map e.toEmbedding
  let hisoF : Flc2Witness.starG ≃g F₀ := SimpleGraph.Iso.map e Flc2Witness.starG
  have hisoApp : ∀ i : Fin 4, hisoF i = e i := fun i =>
    SimpleGraph.Iso.map_apply e Flc2Witness.starG i
  have hF₀adj : ∀ u v : Fin 4, F₀.Adj (e u) (e v) ↔ Flc2Witness.starG.Adj u v := by
    intro u v
    have := hisoF.map_adj_iff (v := u) (w := v)
    simpa [hisoApp] using this
  have hF₀ac : F₀.IsAcyclic := (hisoF.symm.isAcyclic_iff).mpr Flc2Witness.starG_isTree.isAcyclic
  have hsurj : ∀ w : (↑Vset : Type), ∃ i : Fin 4, e i = w := fun w => e.surjective w
  have hF₀dec : DecidableRel F₀.Adj := Classical.decRel _
  
  have hdeg : ∀ i : Fin 4, F₀.degree (e i) = Flc2Witness.starG.degree i := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    have hnbhd : F₀.neighborFinset (e i) = (Flc2Witness.starG.neighborFinset i).image e := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
      constructor
      · intro hw
        obtain ⟨j, rfl⟩ := e.surjective w
        exact ⟨j, by rw [SimpleGraph.mem_neighborFinset]; exact (hF₀adj i j).mp hw, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rw [SimpleGraph.mem_neighborFinset] at hj
        exact (hF₀adj i j).mpr hj
    rw [hnbhd, Finset.card_image_of_injective _ e.injective]
  refine osf_peeledBoxForest_of_acyclic ω n Vset ⟨e 0⟩ F₀ hF₀ac
    (fun _ => e 0) (fun _ i => e i.succ) ?_ ?_ ?_ ?_
  · 
    intro u v huv
    obtain ⟨iu, rfl⟩ := hsurj u
    obtain ⟨iv, rfl⟩ := hsurj v
    rw [hF₀adj] at huv
    rw [Flc2Witness.starG, fromRel_adj] at huv
    obtain ⟨hne, hor⟩ := huv
    rw [heval, heval]
    fin_cases iu <;> fin_cases iv <;>
      simp only [hlab] <;>
      first
        | exact hadj 0 | exact hadj 1 | exact hadj 2
        | exact (hadj 0).symm | exact (hadj 1).symm | exact (hadj 2).symm
        | (exfalso; revert hor; simp only [Flc2Witness.starE]; decide)
  · 
    intro v
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg]
    fin_cases i <;> decide
  · 
    intro x' hx'box htri'
    have hxx : x' = x := hsingle x' hx'box htri'
    subst x'
    refine ⟨?_, ?_, hsep⟩
    · change (e 0 : Site d) = x; rw [heval]
    · intro i
      refine ⟨?_, ?_⟩
      · 
        change F₀.Reachable (e 0) (e i.succ)
        refine Adj.reachable ?_
        rw [hF₀adj, Flc2Witness.starG, fromRel_adj]
        exact ⟨(Fin.succ_ne_zero i).symm, Or.inl (Or.inl ⟨rfl, Fin.succ_ne_zero i⟩)⟩
      · change e i.succ ≠ e 0
        intro hh; exact Fin.succ_ne_zero i (e.injective hh)
  · 
    intro v hv
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg] at hv
    fin_cases i
    · exact absurd hv (by decide)
    · rw [heval]; exact habdry 0
    · rw [heval]; exact habdry 1
    · rw [heval]; exact habdry 2


theorem osf_singleTree_refutable_forest_survives (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y : Site d} (hxbox : x ∈ box d n) (hxtri : IsTrifurcation d ω x)
    (hybox : y ∈ box d n) (hytri : IsTrifurcation d ω y) (hsep : ¬ Connected d ω x y) :
    ¬ bpr_TreeForestData ω n :=
  bst_treeForestData_refutable_of_twoClusters ω n hxbox hxtri hybox hytri hsep


end Percolation
end StatMech
