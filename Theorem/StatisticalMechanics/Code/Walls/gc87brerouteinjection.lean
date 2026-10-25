/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc86brerouteinjection.Part4
import Def.StatisticalMechanics.Code.Walls.gc87brerouteinjection
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gc87b_connK_mono (ends : ι → Sym2 W) {K R : Finset ι} (hKR : K ⊆ R) {a b : W}
    (h : connK ends K a b) : connK ends R a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      obtain ⟨i, hi, ha, hb, hne⟩ := hstep
      exact ih.tail ⟨i, hKR hi, ha, hb, hne⟩


theorem gc87b_ncount_xg_eq (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {x g : W} (hxg : x ≠ g) :
    gc86b_ncount ends R {x, g}
      = if connK ends R x g then gc86b_ncount ends R ∅ else 0 := by
  by_cases hconn : connK ends R x g
  · rw [if_pos hconn, gc86b_ncount_conn_eq ends R hxg hconn]
  · rw [if_neg hconn]
    
    unfold gc86b_ncount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro K hK
    rw [Finset.mem_powerset] at hK
    intro hKsrc
    
    have hKnd : ∀ i ∈ K, ¬ (ends i).IsDiag := fun i hi => hnd i (hK hi)
    have hx_odd : Odd (degK ends K x) := by
      rw [← RandomCurrent.mem_sources, hKsrc]; simp
    have hbdry : ∀ w, Odd (degK ends K w) → w = x ∨ w = g := by
      intro w hw
      have : w ∈ sources ends K := by rw [RandomCurrent.mem_sources]; exact hw
      rw [hKsrc] at this
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    have hconnK : connK ends K x g := RandomCurrent.path_exists ends K hKnd x g hx_odd hbdry hxg
    
    exact hconn (gc87b_connK_mono ends hK hconnK)


theorem gc87b_cogxg_fiber_conn (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W} (hxg : x ≠ g) :
    gc85b_pcount ends m {o, g} {x, g}
      = ∑ K₁ ∈ (m.powerset.filter (fun K => sources ends K = {o, g})).filter
          (fun K₁ => connK ends (m \ K₁) x g),
        gc86b_ncount ends (m \ K₁) ∅ := by
  rw [gc85b_pcount_fiber ends m {o, g} {x, g}]
  
  rw [Finset.sum_congr rfl (fun K₁ hK₁ => by
        simp only [Finset.mem_filter, Finset.mem_powerset] at hK₁
        have hRnd : ∀ i ∈ m \ K₁, ¬ (ends i).IsDiag := fun i hi => hnd i (Finset.mem_sdiff.1 hi).1
        exact gc87b_ncount_xg_eq ends (m \ K₁) hRnd hxg)]
  
  rw [← Finset.sum_filter, Finset.filter_filter]


theorem gc87b_fiber_slack_eq_of_allConn (ends : ι → Sym2 W) (R : Finset ι) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hcx : connK ends R o x) (hcy : connK ends R o y) (hcg : connK ends R o g) :
    (gc86b_ncount ends R {o, g} : ℤ) + (gc86b_ncount ends R {o, x} : ℤ)
        + (gc86b_ncount ends R {o, y} : ℤ) - (gc86b_ncount ends R ∅ : ℤ)
      = 2 * (gc86b_ncount ends R ∅ : ℤ) := by
  have hg := gc86b_ncount_conn_eq ends R hog hcg
  have hx := gc86b_ncount_conn_eq ends R hox hcx
  have hy := gc86b_ncount_conn_eq ends R hoy hcy
  rw [hg, hx, hy]; ring


theorem gc87b_slack_fiber (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc87b_slack ends m o x y g
      = ∑ K₁ ∈ m.powerset.filter (fun K => sources ends K = ∅),
          ((gc86b_ncount ends (m \ K₁) {o, g} : ℤ) + (gc86b_ncount ends (m \ K₁) {o, x} : ℤ)
            + (gc86b_ncount ends (m \ K₁) {o, y} : ℤ) - (gc86b_ncount ends (m \ K₁) ∅ : ℤ)) := by
  unfold gc87b_slack
  rw [gc85b_pcount_fiber ends m ∅ {o, g}, gc85b_pcount_fiber ends m ∅ {o, x},
      gc85b_pcount_fiber ends m ∅ {o, y}, gc85b_pcount_fiber ends m ∅ ∅]
  push_cast
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]


theorem gc87b_T3_eq_sum_if (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    (gc87b_T3 ends m o x y g : ℤ)
      = ∑ K₁ ∈ m.powerset.filter (fun K => sources ends K = ∅),
          (if connK ends (m \ K₁) o x ∧ connK ends (m \ K₁) o y ∧ connK ends (m \ K₁) o g
            then (gc86b_ncount ends (m \ K₁) ∅ : ℤ) else 0) := by
  unfold gc87b_T3
  push_cast
  rw [Finset.sum_filter]


theorem gc87b_two_T3_le_slack (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    2 * (gc87b_T3 ends m o x y g : ℤ) ≤ gc87b_slack ends m o x y g := by
  rw [gc87b_slack_fiber ends m o x y g]
  rw [show (2 * (gc87b_T3 ends m o x y g : ℤ))
        = ∑ K₁ ∈ m.powerset.filter (fun K => sources ends K = ∅),
            (if connK ends (m \ K₁) o x ∧ connK ends (m \ K₁) o y ∧ connK ends (m \ K₁) o g
              then 2 * (gc86b_ncount ends (m \ K₁) ∅ : ℤ) else 0) from ?_]
  · 
    refine Finset.sum_le_sum (fun K₁ hK₁ => ?_)
    simp only [Finset.mem_filter, Finset.mem_powerset] at hK₁
    obtain ⟨hK₁m, hK₁src⟩ := hK₁
    
    have hRsrc : sources ends (m \ K₁) = ({o, x, y, g} : Finset W) := by
      rw [gc86b_sources_sdiff_of_empty ends hK₁m hK₁src, hsrc]
    have hRnd : ∀ i ∈ m \ K₁, ¬ (ends i).IsDiag := fun i hi => hnd i (Finset.mem_sdiff.1 hi).1
    
    have hnn : 0 ≤ (gc86b_ncount ends (m \ K₁) {o, g} : ℤ) + (gc86b_ncount ends (m \ K₁) {o, x} : ℤ)
        + (gc86b_ncount ends (m \ K₁) {o, y} : ℤ) - (gc86b_ncount ends (m \ K₁) ∅ : ℤ) := by
      have := gc86b_strong_of_conn ends (m \ K₁) hRnd hRsrc hox hoy hog
      
      zify at this; linarith
    by_cases hconn : connK ends (m \ K₁) o x ∧ connK ends (m \ K₁) o y ∧ connK ends (m \ K₁) o g
    · rw [if_pos hconn]
      obtain ⟨hcx, hcy, hcg⟩ := hconn
      rw [gc87b_fiber_slack_eq_of_allConn ends (m \ K₁) hox hoy hog hcx hcy hcg]
    · rw [if_neg hconn]; exact hnn
  · rw [gc87b_T3_eq_sum_if ends m o x y g, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun K₁ hK₁ => ?_)
    by_cases hconn : connK ends (m \ K₁) o x ∧ connK ends (m \ K₁) o y ∧ connK ends (m \ K₁) o g
    · rw [if_pos hconn, if_pos hconn]
    · rw [if_neg hconn, if_neg hconn, mul_zero]


end StatMech.Walls
