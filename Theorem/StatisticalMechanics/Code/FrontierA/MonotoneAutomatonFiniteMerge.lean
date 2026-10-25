/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInsertion.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonFiniteMerge
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


theorem mem_boxFinsetBK_iff {n : ℕ} {x : Site d} :
    x ∈ boxFinsetBK d n ↔ x ∈ box d n := by
  simp [boxFinsetBK]


theorem box_subset_box_succ (n : ℕ) : box d n ⊆ box d (n + 1) := by
  intro x hx i
  exact le_trans (hx i) (Nat.le_succ n)


theorem mem_box_of_forceSitesOccupied_true_of_false (n : ℕ)
    (eta : ConfigSpace (Site d)) (x : Site d)
    (hforced : forceSitesOccupied (boxFinsetBK d n) eta x = true)
    (hclosed : eta x = false) : x ∈ box d n := by
  by_contra hx
  have hx' : x ∉ boxFinsetBK d n := by
    simpa [mem_boxFinsetBK_iff] using hx
  rw [forceSitesOccupied_apply, if_neg hx', hclosed] at hforced
  contradiction


theorem openSubgraph_siteForce_eq_forceOpen (n : ℕ)
    (eta : ConfigSpace (Site d)) :
    openSubgraph d
        (forceOpenFinset (siteForceEdges n eta) (siteToBond eta)) =
      openSubgraph d
        (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) := by
  ext x y
  simp only [openSubgraph_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    by_cases hmem : s(x, y) ∈ siteForceEdges n eta
    · have hnew :
          siteToBond (forceSitesOccupied (boxFinsetBK d n) eta) s(x, y) = true := by
        simpa [siteForceEdges] using (Finset.mem_filter.mp hmem).2
      exact hnew
    · rw [forceOpenFinset_of_notMem hmem] at hopen
      have hmono : siteToBond eta ≤
          siteToBond (forceSitesOccupied (boxFinsetBK d n) eta) := by
        apply siteToBond_mono
        intro z
        by_cases hz : z ∈ boxFinsetBK d n
        · simp [forceSitesOccupied, hz]
        · simp [forceSitesOccupied, hz]
      exact Bool.eq_true_of_true_le (hopen ▸ hmono s(x, y))
  · rintro ⟨hadj, hnew⟩
    refine ⟨hadj, ?_⟩
    by_cases hold : siteToBond eta s(x, y) = true
    · unfold forceOpenFinset
      split <;> simp [hold]
    · have hxyNew :
          forceSitesOccupied (boxFinsetBK d n) eta x = true ∧
            forceSitesOccupied (boxFinsetBK d n) eta y = true := by
        simpa [siteToBond_mk, Bool.and_eq_true] using hnew
      have hxyOld : eta x = false ∨ eta y = false := by
        cases hxOld : eta x with
        | false => exact Or.inl rfl
        | true =>
            cases hyOld : eta y with
            | false => exact Or.inr rfl
            | true =>
                exfalso
                apply hold
                simp [siteToBond_mk, hxOld, hyOld]
      have hbox : x ∈ box d (n + 1) ∧ y ∈ box d (n + 1) := by
        rcases hxyOld with hxOld | hyOld
        · have hxBox : x ∈ box d n :=
            mem_box_of_forceSitesOccupied_true_of_false n eta x hxyNew.1 hxOld
          exact ⟨box_subset_box_succ n hxBox, adj_box_step hxBox hadj⟩
        · have hyBox : y ∈ box d n :=
            mem_box_of_forceSitesOccupied_true_of_false n eta y hxyNew.2 hyOld
          exact ⟨adj_box_step hyBox hadj.symm, box_subset_box_succ n hyBox⟩
      have hedge : s(x, y) ∈ siteForceEdges n eta := by
        rw [siteForceEdges, Finset.mem_filter]
        exact ⟨mk_mem_boxEdges hbox.1 hbox.2 hadj, hnew⟩
      exact forceOpenFinset_of_mem hedge (siteToBond eta)


theorem connected_siteForce_iff_forceOpen (n : ℕ)
    (eta : ConfigSpace (Site d)) (x y : Site d) :
    Connected d (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) x y ↔
      Connected d
        (forceOpenFinset (siteForceEdges n eta) (siteToBond eta)) x y := by
  unfold Connected
  rw [openSubgraph_siteForce_eq_forceOpen]


theorem cluster_siteForce_eq_forceOpen (n : ℕ)
    (eta : ConfigSpace (Site d)) (x : Site d) :
    cluster d (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) x =
      cluster d (forceOpenFinset (siteForceEdges n eta) (siteToBond eta)) x := by
  ext y
  exact connected_siteForce_iff_forceOpen n eta x y


theorem numInfiniteClusters_siteForce_eq_forceOpen (n : ℕ)
    (eta : ConfigSpace (Site d)) :
    numInfiniteClusters d
        (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) =
      numInfiniteClusters d
        (forceOpenFinset (siteForceEdges n eta) (siteToBond eta)) := by
  unfold numInfiniteClusters
  apply congrArg Set.encard
  ext C
  simp only [infiniteClusters, Set.mem_setOf_eq]
  constructor <;> rintro ⟨hC, x, rfl⟩
  · exact ⟨hC, x, cluster_siteForce_eq_forceOpen n eta x⟩
  · exact ⟨hC, x, (cluster_siteForce_eq_forceOpen n eta x).symm⟩


theorem siteForce_box_connected (n : ℕ) (eta : ConfigSpace (Site d))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    Connected d (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) x y := by
  have hle : forceOpenFinset (boxEdges d n) (siteToBond eta) ≤
      siteToBond (forceSitesOccupied (boxFinsetBK d n) eta) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
        by_cases he : s(u, v) ∈ boxEdges d n
        · have huv := mem_boxEdges_iff.mp he
          simp [forceOpenFinset, he, siteToBond_mk, forceSitesOccupied,
            mem_boxFinsetBK_iff.mpr huv.1, mem_boxFinsetBK_iff.mpr huv.2.1]
        · rw [forceOpenFinset_of_notMem he]
          exact siteToBond_mono (fun z => by
            by_cases hz : z ∈ boxFinsetBK d n <;> simp [forceSitesOccupied, hz]) s(u, v)
  exact connected_mono hle (box_allOpen_connected (siteToBond eta) hx hy)


theorem numInfiniteClusters_siteForce_lt_of_twoMeetBox (n : ℕ)
    (eta : ConfigSpace (Site d))
    (hfin : numInfiniteClusters d (siteToBond eta) ≠ ⊤)
    {x y : Site d} (hxbox : x ∈ box d n) (hybox : y ∈ box d n)
    (hx : (cluster d (siteToBond eta) x).Infinite)
    (hy : (cluster d (siteToBond eta) y).Infinite)
    (hne : cluster d (siteToBond eta) x ≠ cluster d (siteToBond eta) y) :
    numInfiniteClusters d
        (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) <
      numInfiniteClusters d (siteToBond eta) := by
  rw [numInfiniteClusters_siteForce_eq_forceOpen]
  exact numInfiniteClusters_lt_of_merge (siteForceEdges n eta) (siteToBond eta)
    hfin x y hx hy hne
    ((connected_siteForce_iff_forceOpen n eta x y).1
      (siteForce_box_connected n eta hxbox hybox))


end StatMech.FrontierA
