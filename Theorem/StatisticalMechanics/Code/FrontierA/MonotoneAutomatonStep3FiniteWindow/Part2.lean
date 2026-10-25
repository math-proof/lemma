/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


@[simp] theorem left_mem_coordinateBetween (x y : Site d) :
    x ∈ coordinateBetween x y := by
  intro i
  exact ⟨min_le_left _ _, le_max_left _ _⟩

@[simp] theorem right_mem_coordinateBetween (x y : Site d) :
    y ∈ coordinateBetween x y := by
  intro i
  exact ⟨min_le_right _ _, le_max_right _ _⟩

theorem coordinateBetween_l1dist_le {x y z : Site d}
    (hz : z ∈ coordinateBetween x y) :
    l1dist d x z ≤ l1dist d x y := by
  unfold l1dist
  apply Finset.sum_le_sum
  intro i hi
  have hzi := hz i
  rcases le_total (x i) (y i) with hxy | hyx
  · simp only [min_eq_left hxy, max_eq_right hxy] at hzi
    omega
  · simp only [min_eq_right hyx, max_eq_left hyx] at hzi
    omega


theorem eq_right_of_mem_coordinateBetween_of_l1dist_eq
    {x y z : Site d} (hz : z ∈ coordinateBetween x y)
    (heq : l1dist d x z = l1dist d x y) : z = y := by
  funext i
  have hzi := hz i
  by_contra hne
  have hstrictTerm : (x i - z i).natAbs < (x i - y i).natAbs := by
    rcases le_total (x i) (y i) with hxy | hyx
    · simp only [min_eq_left hxy, max_eq_right hxy] at hzi
      omega
    · simp only [min_eq_right hyx, max_eq_left hyx] at hzi
      omega
  have hleTerms : ∀ j, (x j - z j).natAbs ≤ (x j - y j).natAbs := by
    intro j
    have hzj := hz j
    rcases le_total (x j) (y j) with hxy | hyx
    · simp only [min_eq_left hxy, max_eq_right hxy] at hzj
      omega
    · simp only [min_eq_right hyx, max_eq_left hyx] at hzj
      omega
  have hsumStrict :
      (∑ j, (x j - z j).natAbs) < ∑ j, (x j - y j).natAbs := by
    exact Finset.sum_lt_sum (fun j _ => hleTerms j)
      ⟨i, Finset.mem_univ i, hstrictTerm⟩
  exact (ne_of_lt hsumStrict) heq

theorem coordinateBetween_finite (x y : Site d) :
    (coordinateBetween x y).Finite := by
  let D := l1dist d x y
  have hsub : coordinateBetween x y ⊆
      (fun w : Site d => x + w) '' box d D := by
    intro z hz
    refine ⟨z - x, ?_, by simp⟩
    intro i
    have hcoord : (z i - x i).natAbs ≤ D := by
      have hterm : (x i - z i).natAbs ≤ l1dist d x z := by
        unfold l1dist
        exact Finset.single_le_sum
          (f := fun j : Fin d => (x j - z j).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have habs : (z i - x i).natAbs = (x i - z i).natAbs := by
        rw [← Int.natAbs_neg]
        congr 1
        ring
      rw [habs]
      exact hterm.trans (coordinateBetween_l1dist_le hz)
    simpa [Pi.sub_apply] using hcoord
  exact ((box_finite d D).image (fun w : Site d => x + w)).subset hsub

theorem mixSite_mem_coordinateBetween (x y : Site d) (k : ℕ) :
    mixSite x y k ∈ coordinateBetween x y := by
  intro i
  simp only [mixSite]
  split_ifs
  · exact ⟨min_le_right _ _, le_max_right _ _⟩
  · exact ⟨min_le_left _ _, le_max_left _ _⟩


theorem coordinateBetween_update_reachable (x y u : Site d)
    (hu : u ∈ coordinateBetween x y) (j : Fin d) :
    ((hypercubicLattice d).induce (coordinateBetween x y)).Reachable
      ⟨u, hu⟩
      ⟨Function.update u j (y j), by
        intro i
        by_cases hij : i = j
        · subst i
          simp
        · simpa [Function.update_of_ne hij] using hu i⟩ := by
  classical
  let v := Function.update u j (y j)
  have hv : v ∈ coordinateBetween x y := by
    intro i
    by_cases hij : i = j
    · subst i
      simp [v]
    · simpa [v, Function.update_of_ne hij] using hu i
  rcases le_total (u j) (y j) with hle | hle
  · obtain ⟨n, hn⟩ := Int.le.dest hle
    have hseg := segment_connectedWithin (coordinateBetween x y) j u n
      (fun t ht => by
        intro i
        by_cases hij : i = j
        · subst i
          simp only [Function.update_self]
          have huj := hu j
          omega
        · simpa [Function.update_of_ne hij] using hu i)
    have hend : Function.update u j (u j + (n : ℤ)) = v := by
      simp [v, hn]
    simpa [v, hend] using hseg
  · obtain ⟨n, hn⟩ := Int.le.dest hle
    have hseg := segment_connectedWithin (coordinateBetween x y) j v n
      (fun t ht => by
        intro i
        by_cases hij : i = j
        · subst i
          simp only [Function.update_self, v]
          have huj := hu j
          omega
        · simpa [v, Function.update_of_ne hij] using hu i)
    have hend : Function.update v j (v j + (n : ℤ)) = u := by
      funext i
      by_cases hij : i = j
      · subst i
        simp [v, hn]
      · simp [v, Function.update_of_ne hij]
    have hrev := hseg.symm
    simpa only [Int.ofNat_zero, add_zero, Function.update_eq_self, hend] using hrev


theorem coordinateBetween_reachable (x y : Site d) :
    ((hypercubicLattice d).induce (coordinateBetween x y)).Reachable
      ⟨x, left_mem_coordinateBetween x y⟩
      ⟨y, right_mem_coordinateBetween x y⟩ := by
  have hreach : ∀ k ≤ d,
      ((hypercubicLattice d).induce (coordinateBetween x y)).Reachable
        ⟨x, left_mem_coordinateBetween x y⟩
        ⟨mixSite x y k, mixSite_mem_coordinateBetween x y k⟩ := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa only [mixSite_zero] using
          (SimpleGraph.Reachable.refl
            (⟨x, left_mem_coordinateBetween x y⟩ : coordinateBetween x y))
    | succ k ih =>
        intro hk
        have hkd : k < d := by omega
        have hstep := coordinateBetween_update_reachable x y
          (mixSite x y k) (mixSite_mem_coordinateBetween x y k) ⟨k, hkd⟩
        have hmix : mixSite x y (k + 1) =
            Function.update (mixSite x y k) ⟨k, hkd⟩ (y ⟨k, hkd⟩) :=
          mixSite_succ hkd
        exact (ih (by omega)).trans (by simpa [hmix] using hstep)
  simpa using hreach d le_rfl


theorem connected_siteToBond_of_coordinateBetween
    (eta : ConfigSpace (Site d)) (x y : Site d)
    (hopen : ∀ z ∈ coordinateBetween x y, eta z = true) :
    Connected d (siteToBond eta) x y := by
  rw [connected_siteToBond_iff]
  let f : (hypercubicLattice d).induce (coordinateBetween x y) →g
      siteOpenGraph eta :=
    { toFun := fun z => z.1
      map_rel' := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        exact ⟨hab, hopen a ha, hopen b hb⟩ }
  exact (coordinateBetween_reachable x y).map f


end StatMech.FrontierA
