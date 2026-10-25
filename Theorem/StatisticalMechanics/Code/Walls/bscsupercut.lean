/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfinfinalclose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcvcutvertex.Part3
import Def.StatisticalMechanics.Code.Walls.bscsupercut
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

#check @bfin_SuperCutBridge


theorem bsc_ediv_zero_iff {L : ℕ} {a : ℤ} :
    (a + (L : ℤ)) / (2 * (L : ℤ) + 1) = 0 ↔ a.natAbs ≤ L := by
  have hb : (0 : ℤ) < 2 * (L : ℤ) + 1 := by positivity
  constructor
  · intro hq
    have h1 : (a + (L : ℤ)) % (2 * (L : ℤ) + 1) = a + (L : ℤ) := by
      have := Int.emod_add_ediv (a + (L : ℤ)) (2 * (L : ℤ) + 1)
      rw [hq] at this; omega
    have h2 : 0 ≤ (a + (L : ℤ)) % (2 * (L : ℤ) + 1) := Int.emod_nonneg _ (by omega)
    have h3 : (a + (L : ℤ)) % (2 * (L : ℤ) + 1) < 2 * (L : ℤ) + 1 := Int.emod_lt_of_pos _ hb
    rw [h1] at h2 h3; omega
  · intro h
    exact Int.ediv_eq_zero_of_lt (by omega) (by omega)


theorem bsc_boxCentre_zero (d L : ℕ) : bsc_IsBoxCentre L (0 : Site d) := by
  intro x
  have hidx0 : bgn_idx L (0 : Site d) = 0 := by
    funext i
    show ((0 : Site d) i + (L : ℤ)) / (2 * (L : ℤ) + 1) = (0 : Site d) i
    simp only [Pi.zero_apply, zero_add]
    exact Int.ediv_eq_zero_of_lt (by positivity) (by omega)
  rw [hidx0, bc61_mem_boxAround, sub_zero, mem_box]
  constructor
  · intro h; funext i
    have : (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) = 0 := (bsc_ediv_zero_iff).mpr (h i)
    simpa [bgn_idx] using this
  · intro h i
    have := congrFun h i
    simp only [bgn_idx, Pi.zero_apply] at this
    exact (bsc_ediv_zero_iff).mp this

#check @bsc_boxCentre_zero


theorem bsc_box_isolated {L : ℕ} {y a : Site d} (ω : ConfigSpace (Sym2 (Site d)))
    (ha : a ∈ bc61_boxAround d L y) (w : Site d) :
    ¬ (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Adj a w := by
  intro hadj
  have hopen : removeSites (bc61_boxAround d L y) ω s(a, w) = true := hadj.2
  unfold removeSites at hopen
  rw [if_pos ⟨a, ha, by rw [Sym2.mem_iff]; left; rfl⟩] at hopen
  exact absurd hopen (by simp)


theorem bsc_notMem_box_of_infinite {L : ℕ} {y a : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    a ∉ bc61_boxAround d L y := by
  intro ha
  
  have hsub : cluster d (removeSites (bc61_boxAround d L y) ω) a ⊆ {a} := by
    intro z hz
    have hr : (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Reachable a z := hz
    obtain ⟨p⟩ := hr
    cases p with
    | nil => exact Set.mem_singleton_iff.mpr rfl
    | cons hadj _ => exact absurd hadj (bsc_box_isolated ω ha _)
  exact hinf (Set.Finite.subset (Set.finite_singleton a) hsub)


theorem bsc_hub_adj_armImage {L : ℕ} {y a : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hy : bsc_IsBoxCentre L y)
    (hinc : bc67_GnIncident ω L y a)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    bgn_idx L a ≠ bgn_idx L y ∧ (bgn_Gn ω L).Adj (bgn_idx L y) (bgn_idx L a) := by
  have haout : a ∉ bc61_boxAround d L y := bsc_notMem_box_of_infinite hinf
  have hne : bgn_idx L a ≠ bgn_idx L y := by
    intro h; exact haout ((hy a).mpr h)
  refine ⟨hne, hne.symm, ?_⟩
  obtain ⟨b, hbbox, hbadj⟩ := hinc
  have hbidx : bgn_idx L b = bgn_idx L y := (hy b).mp hbbox
  exact ⟨b, a, hbidx, rfl, hbadj⟩


theorem bsc_superReach_of_siteConn {L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hy : bsc_IsBoxCentre L y) {a b : Site d}
    (h : Connected d (removeSites (bc61_boxAround d L y) ω) a b) :
    (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable (bgn_idx L a) (bgn_idx L b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons x z b hadj q ih =>
    refine Reachable.trans ?_ ih
    
    have hopen : removeSites (bc61_boxAround d L y) ω s(x, z) = true := hadj.2
    have hcond : ¬ ∃ t ∈ bc61_boxAround d L y, t ∈ s(x, z) := by
      intro hh; unfold removeSites at hopen; rw [if_pos hh] at hopen; exact absurd hopen (by simp)
    have hxout : x ∉ bc61_boxAround d L y := fun hx => hcond ⟨x, hx, by rw [Sym2.mem_iff]; left; rfl⟩
    have hzout : z ∉ bc61_boxAround d L y := fun hz => hcond ⟨z, hz, by rw [Sym2.mem_iff]; right; rfl⟩
    have hxne : bgn_idx L x ≠ bgn_idx L y := fun hh => hxout ((hy x).mpr hh)
    have hzne : bgn_idx L z ≠ bgn_idx L y := fun hh => hzout ((hy z).mpr hh)
    
    have hωopen : (openSubgraph d ω).Adj x z := by
      refine ⟨hadj.1, ?_⟩
      have hle := bc61_removeBox_le d L y ω s(x, z)
      rw [hopen] at hle
      revert hle; cases ω s(x, z) <;> simp
    by_cases hxz : bgn_idx L x = bgn_idx L z
    · exact hxz ▸ Reachable.refl _
    · have hedge : (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Adj (bgn_idx L x) (bgn_idx L z) :=
        ⟨⟨hxz, x, z, rfl, rfl, hωopen⟩, hxne, hzne⟩
      exact hedge.reachable

#check @bsc_hub_adj_armImage
#check @bsc_superReach_of_siteConn


theorem bsc_ediv_eq_iff {L : ℕ} {a m : ℤ} :
    (a + (L : ℤ)) / (2 * (L : ℤ) + 1) = m ↔ (a - (2 * (L : ℤ) + 1) * m).natAbs ≤ L := by
  have hb : (0 : ℤ) < 2 * (L : ℤ) + 1 := by positivity
  have hkey : (a + (L : ℤ)) / (2 * (L : ℤ) + 1)
      = (a - (2 * (L : ℤ) + 1) * m + (L : ℤ)) / (2 * (L : ℤ) + 1) + m := by
    rw [← Int.add_mul_ediv_right _ m (by omega : (2 * (L : ℤ) + 1) ≠ 0)]
    congr 1; ring
  rw [hkey]
  constructor
  · intro h; exact (bsc_ediv_zero_iff).mp (by omega)
  · intro h; have := (bsc_ediv_zero_iff).mpr h; omega


theorem bsc_fiber_finite (L : ℕ) (j : Site d) : {x : Site d | bgn_idx L x = j}.Finite := by
  set c : Site d := fun i => (2 * (L : ℤ) + 1) * j i with hc
  have hset : {x : Site d | bgn_idx L x = j} = ↑(bc61_boxAround d L c) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_coe, bc61_mem_boxAround, mem_box]
    constructor
    · intro h i
      have := congrFun h i
      simp only [bgn_idx] at this
      have h2 := (bsc_ediv_eq_iff).mp this
      simpa [Pi.sub_apply, hc] using h2
    · intro h; funext i
      simp only [bgn_idx]
      refine (bsc_ediv_eq_iff).mpr ?_
      have := h i
      simpa [Pi.sub_apply, hc] using this
  rw [hset]; exact (bc61_boxAround d L c).finite_toSet


theorem bsc_deleteWalk_support_avoid {V : Type*} {G : SimpleGraph V} {t : V} :
    ∀ {u v : V} (p : (bkg_deleteVertex G t).Walk u v), u ≠ t → t ∉ p.support := by
  intro u v p
  induction p with
  | nil => intro hu; simpa using hu.symm
  | @cons u z v hadj q ih =>
    intro hu
    rw [Walk.support_cons, List.mem_cons]; push_neg
    exact ⟨hu.symm, ih hadj.2.2⟩


theorem bsc_ray34_of_deleteReach {V : Type*} {G : SimpleGraph V} {t u v : V}
    (hu : u ≠ t) (h : (bkg_deleteVertex G t).Reachable u v) :
    ray34_AvoidReach G {t} u v := by
  obtain ⟨p⟩ := h
  have hle : bkg_deleteVertex G t ≤ G := fun a b hab => hab.1
  refine ⟨p.mapLe hle, ?_⟩
  intro w hw
  rw [Walk.support_mapLe_eq_support] at hw
  simp only [Set.mem_singleton_iff]
  intro hwt; subst hwt
  exact bsc_deleteWalk_support_avoid p hu hw


theorem bsc_arm_ray_infinite {L : ℕ} {y a : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hy : bsc_IsBoxCentre L y)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} (bgn_idx L a)).Infinite := by
  have haout : a ∉ bc61_boxAround d L y := bsc_notMem_box_of_infinite hinf
  have haidx : bgn_idx L a ≠ bgn_idx L y := fun h => haout ((hy a).mpr h)
  
  have himg : (bgn_idx L) '' (cluster d (removeSites (bc61_boxAround d L y) ω) a)
      ⊆ ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} (bgn_idx L a) := by
    rintro _ ⟨c, hc, rfl⟩
    have hconn : Connected d (removeSites (bc61_boxAround d L y) ω) a c := hc
    have hreach := bsc_superReach_of_siteConn hy hconn
    exact bsc_ray34_of_deleteReach haidx hreach
  refine Set.Infinite.mono himg ?_
  
  intro hfin
  apply hinf
  have hsub : cluster d (removeSites (bc61_boxAround d L y) ω) a
      ⊆ ⋃ j ∈ (bgn_idx L) '' (cluster d (removeSites (bc61_boxAround d L y) ω) a),
          {x : Site d | bgn_idx L x = j} := by
    intro x hx
    exact Set.mem_biUnion ⟨x, hx, rfl⟩ rfl
  exact Set.Finite.subset (hfin.biUnion (fun j _ => bsc_fiber_finite L j)) hsub

#check @bsc_arm_ray_infinite


end StatMech.Walls
