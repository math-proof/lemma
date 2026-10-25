/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard.Part3
import Def.StatisticalMechanics.Code.Walls.bc19menger.Part3


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}


theorem bc19_aFan_extract [Fintype V] {A B S : Set V}
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hSsep : bc16_IsSeparator G A B S)
    (hH : bc17_HardDir (bc17_restr G (bc18_AReach G A S)) A S) :
    Nonempty (bc19_AFan G A S (bc18_AReach G A S) k) := by
  have F := (bc18_aside_fan hmin hSsep hH).some
  set RA := bc18_AReach G A S with hRA
  have hregF : ∀ i, ∀ z ∈ (F.p i).support, z ∈ RA := fun i z hz =>
    bc17_restr_support_subset G RA (bc18_subset_AReach G A S (F.ha i)) (F.p i) z hz
  set F' := bc17_familyMapLe (bc17_restr_le G RA) F with hF'
  have hregF' : ∀ i, ∀ z ∈ (F'.p i).support, z ∈ RA := by
    intro i z hz
    rw [hF'] at hz; simp only [bc17_familyMapLe] at hz
    rw [Walk.support_mapLe_eq_support] at hz; exact hregF i z hz
  exact ⟨bc19_AFan_of_family F' hregF'⟩


theorem bc19_trivFan [Fintype V] {B S : Set V} (hS : S.ncard = k) (hSB : S ⊆ B) :
    Nonempty (bc19_AFan G B S S k) := by
  obtain ⟨f, hinj, hf⟩ := bc17_exists_finInj_of_le_ncard (Set.toFinite S) (le_of_eq hS.symm)
  exact ⟨{
    a := f
    c := f
    q := fun _ => Walk.nil
    ha := fun i => hSB (hf i)
    hc := hf
    hq := fun _ => Walk.IsPath.nil
    hmeet := by
      intro i z hz _
      rw [Walk.support_nil, List.mem_singleton] at hz; exact hz
    hreg := by
      intro i z hz
      rw [Walk.support_nil, List.mem_singleton] at hz; exact hz ▸ hf i
    hdisj := by
      intro i j hij z hzi hzj
      rw [Walk.support_nil, List.mem_singleton] at hzi hzj
      exact hij (hinj (hzi.symm.trans hzj)) }⟩


omit [DecidableEq V] in

theorem bc19_lastEdge {a s : V} (Q : G.Walk a s) (hne : a ≠ s) :
    ∃ u, G.Adj u s ∧ u ∈ Q.support := by
  induction Q with
  | nil => exact absurd rfl hne
  | @cons a b s hadj t ih =>
      by_cases hbs : b = s
      · subst hbs; exact ⟨a, hadj, Walk.start_mem_support _⟩
      · obtain ⟨u, hu, hut⟩ := ih hbs
        exact ⟨u, hu, by rw [Walk.support_cons]; exact List.mem_cons.2 (Or.inr hut)⟩

omit [DecidableEq V] in


theorem bc19_essential [Fintype V] {A B S : Set V} {s : V}
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hScard : S.ncard = k) (hsS : s ∈ S) :
    ¬ bc16_IsSeparator G A B (S \ {s}) := by
  intro hsep
  have hle := hmin _ hsep
  have : (S \ {s}).ncard < S.ncard :=
    Set.ncard_lt_ncard ⟨Set.diff_subset, fun h => (h hsS).2 rfl⟩ (Set.toFinite S)
  rw [hScard] at this; omega


theorem bc19_Bside_strict_of_notSubsetA [Fintype V] {A B S : Set V}
    (hSsep : bc16_IsSeparator G A B S)
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hScard : S.ncard = k)
    (hnsub : ¬ S ⊆ A) :
    (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < G.edgeSet.ncard := by
  obtain ⟨s, hsS, hsA⟩ : ∃ s ∈ S, s ∉ A := by
    by_contra hc; push Not at hc; exact hnsub (fun s hs => hc s hs)
  have hess := bc19_essential hmin hScard hsS
  obtain ⟨a, ha, Q0, hQ0⟩ := bc18_mem_AReach_of_essential hSsep hess
  set Q := Q0.bypass with hQdef
  have hQpath : Q.IsPath := Q0.bypass_isPath
  have hQmeet : ∀ z ∈ Q.support, z ∈ S → z = s := fun z hz => hQ0 z (Q0.support_bypass_subset hz)
  have hane : a ≠ s := fun h => hsA (h ▸ ha)
  obtain ⟨u, hAdj, huQ⟩ := bc19_lastEdge Q hane
  have huS : u ∉ S := fun huS => hAdj.ne (hQmeet u huQ huS)
  have huRA : u ∈ bc18_AReach G A S := bc18_mem_AReach_of_mem_support ha hQpath hQmeet huQ
  have huRB : u ∉ bc18_AReach G B S := fun huRB =>
    huS (bc18_AReach_inter_subset hSsep ⟨huRA, huRB⟩)
  exact bc17_restr_edgeSet_ncard_lt G (bc18_AReach G B S) (x := s) (y := u) hAdj.symm huRB


theorem bc19_Aside_strict_of_notSubsetB [Fintype V] {A B S : Set V}
    (hSsep : bc16_IsSeparator G A B S)
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hScard : S.ncard = k)
    (hnsub : ¬ S ⊆ B) :
    (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < G.edgeSet.ncard :=
  bc19_Bside_strict_of_notSubsetA (bc16_separator_symm hSsep)
    (fun C hC => hmin C (bc16_separator_symm hC)) hScard hnsub


end StatMech.Walls
