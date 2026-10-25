/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Def.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

open StatMech.Percolation

variable {d : ℕ}


theorem gv_self_mem_ball (x : Site d) : x ∈ gvBall x := Finset.mem_insert_self _ _


theorem gv_nbr_mem_ball {x y : Site d} (hadj : (hypercubicLattice d).Adj x y) :
    y ∈ gvBall x := by
  rw [hypercubicLattice_adj] at hadj
  
  obtain ⟨i, hi1, hi0⟩ : ∃ i, (x i - y i).natAbs = 1 ∧ ∀ j, j ≠ i → x j = y j := by
    rcases Finset.exists_ne_zero_of_sum_ne_zero (by rw [hadj]; norm_num :
        (∑ i, (x i - y i).natAbs) ≠ 0) with ⟨i, _, hine⟩
    have hi1 : (x i - y i).natAbs = 1 := by
      by_contra hc
      have hge : 2 ≤ (x i - y i).natAbs := by omega
      have : 2 ≤ ∑ j, (x j - y j).natAbs :=
        le_trans hge (Finset.single_le_sum (f := fun j => (x j - y j).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      omega
    refine ⟨i, hi1, fun j hj => ?_⟩
    by_contra hjne
    have hjpos : 1 ≤ (x j - y j).natAbs := by
      have : x j - y j ≠ 0 := sub_ne_zero.mpr hjne
      omega
    have hsum2 : (x i - y i).natAbs + (x j - y j).natAbs ≤ ∑ k, (x k - y k).natAbs := by
      have := Finset.sum_le_sum_of_subset (s := ({i, j} : Finset (Fin d)))
        (t := (Finset.univ : Finset (Fin d))) (f := fun k => (x k - y k).natAbs)
        (Finset.subset_univ _)
      rwa [Finset.sum_pair (Ne.symm hj)] at this
    omega
  
  rw [gvBall]
  refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩)
  have hxy : x i - y i = 1 ∨ x i - y i = -1 := by
    rcases Int.natAbs_eq_iff.mp hi1 with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  rcases hxy with h | h
  · 
    refine Finset.mem_insert_of_mem (Finset.mem_singleton.mpr ?_)
    funext j
    by_cases hji : j = i
    · subst hji; simp only [Pi.sub_apply, gvUnit, if_true]; omega
    · simp only [Pi.sub_apply, gvUnit, if_neg hji, sub_zero]; exact (hi0 j hji).symm
  · 
    have hyeq : y = x + gvUnit d i := by
      funext j
      by_cases hji : j = i
      · subst hji; simp only [Pi.add_apply, gvUnit, if_true]; omega
      · simp only [Pi.add_apply, gvUnit, if_neg hji, add_zero]; exact (hi0 j hji).symm
    rw [hyeq]; exact Finset.mem_insert_self _ _


theorem gv_mk_mem_bondTouch {S : Finset (Site d)} {x y : Site d}
    (hadj : (hypercubicLattice d).Adj x y) (htouch : x ∈ S ∨ y ∈ S) :
    s(x, y) ∈ gvBondTouch S := by
  rw [gvBondTouch, Finset.mem_image]
  refine ⟨(x, y), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨?_, ?_⟩, hadj, htouch⟩
  · rw [gvCand, Finset.mem_biUnion]
    rcases htouch with h | h
    · exact ⟨x, h, gv_self_mem_ball x⟩
    · exact ⟨y, h, gv_nbr_mem_ball hadj.symm⟩
  · rw [gvCand, Finset.mem_biUnion]
    rcases htouch with h | h
    · exact ⟨x, h, gv_nbr_mem_ball hadj⟩
    · exact ⟨y, h, gv_self_mem_ball y⟩


theorem gv_bondTouch_subset_edgeSet (S : Finset (Site d)) :
    ∀ e ∈ gvBondTouch S, e ∈ (hypercubicLattice d).edgeSet := by
  intro e he
  rw [gvBondTouch, Finset.mem_image] at he
  obtain ⟨p, hp, rfl⟩ := he
  rw [Finset.mem_filter] at hp
  rw [SimpleGraph.mem_edgeSet]
  exact hp.2.1


theorem gv_bondTouch_subset {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout) :
    gvBondTouch Sin ⊆ gvBondTouch Sout := by
  intro e he
  rw [gvBondTouch, Finset.mem_image] at he
  obtain ⟨p, hp, rfl⟩ := he
  rw [Finset.mem_filter] at hp
  obtain ⟨_, hadj, htouch⟩ := hp
  refine gv_mk_mem_bondTouch hadj ?_
  rcases htouch with h | h
  · exact Or.inl (hsub h)
  · exact Or.inr (hsub h)


end Ising
end StatMech
