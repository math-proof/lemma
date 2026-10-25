/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part6
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem crossExt_open_inner (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {u v : boxVerts d (n+1)} (h : crossExt d n ω s(u, v) = true) :
    IsInnerVert d n u ∧ IsInnerVert d n v := by
  unfold crossExt at h
  split at h
  · rename_i hmem
    obtain ⟨e, he⟩ := hmem
    
    refine Sym2.inductionOn e (fun a b hab => ?_) he
    rw [innerEdge, Sym2.map_mk] at hab
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2
      exact ⟨isInnerVert_boxVertIncl d n a, isInnerVert_boxVertIncl d n b⟩
    · subst h1; subst h2
      exact ⟨isInnerVert_boxVertIncl d n b, isInnerVert_boxVertIncl d n a⟩
  · exact absurd h (by simp)


theorem crossWiredGraph_not_adj_of_annulus (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {v : boxVerts d (n+1)}
    (hv : ¬ IsInnerVert d n v) (w : boxVerts d (n+1)) :
    ¬ (crossWiredGraph d n ω).Adj v w := by
  intro h
  rw [crossWiredGraph, wiredGraph_adj] at h
  rcases h with ⟨_, hopen⟩ | ⟨_, hbdry, _⟩
  · exact hv (crossExt_open_inner d n ω hopen).1
  · exact hv hbdry.1


theorem crossExt_innerEdge_pair (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (x y : boxVerts d n) :
    crossExt d n ω s(boxVertIncl d n x, boxVertIncl d n y) = ω s(x, y) := by
  have h : s(boxVertIncl d n x, boxVertIncl d n y) = innerEdge d n s(x, y) := by
    rw [innerEdge, Sym2.map_mk]
  rw [h, crossExt_innerEdge]


theorem crossWiredGraph_adj_boxVertIncl (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (x y : boxVerts d n) :
    (crossWiredGraph d n ω).Adj (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (wiredGraph (boxGraph d n) (boxBoundary d n) ω).Adj x y := by
  rw [crossWiredGraph, wiredGraph_adj, wiredGraph_adj, boxGraph_adj_boxVertIncl,
    crossExt_innerEdge_pair]
  constructor
  · rintro (⟨hadj, hopen⟩ | ⟨hne, hbx, hby⟩)
    · exact Or.inl ⟨hadj, hopen⟩
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · exact fun h => hne (by rw [h])
      · exact (innerBdry_boxVertIncl d n x).mp hbx
      · exact (innerBdry_boxVertIncl d n y).mp hby
  · rintro (⟨hadj, hopen⟩ | ⟨hne, hbx, hby⟩)
    · exact Or.inl ⟨hadj, hopen⟩
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · exact fun h => hne (boxVertIncl_injective d n h)
      · exact (innerBdry_boxVertIncl d n x).mpr hbx
      · exact (innerBdry_boxVertIncl d n y).mpr hby


theorem crossWiredGraph_adj_inner_right (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {u w : boxVerts d (n+1)}
    (hu : IsInnerVert d n u) (h : (crossWiredGraph d n ω).Adj u w) :
    IsInnerVert d n w := by
  rw [crossWiredGraph, wiredGraph_adj] at h
  rcases h with ⟨_, hopen⟩ | ⟨_, _, hbw⟩
  · exact (crossExt_open_inner d n ω hopen).2
  · exact hbw.1


theorem crossWiredGraph_reachable_inner (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {u w : boxVerts d (n+1)}
    (hu : IsInnerVert d n u) (h : (crossWiredGraph d n ω).Reachable u w) :
    IsInnerVert d n w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hu
  | tail _ hadj ih => exact crossWiredGraph_adj_inner_right d n ω ih hadj


theorem crossWiredGraph_reachable_of_inner (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {x y : boxVerts d n}
    (h : (wiredGraph (boxGraph d n) (boxBoundary d n) ω).Reachable x y) :
    (crossWiredGraph d n ω).Reachable (boxVertIncl d n x) (boxVertIncl d n y) := by
  let f : (wiredGraph (boxGraph d n) (boxBoundary d n) ω) →g (crossWiredGraph d n ω) :=
    { toFun := boxVertIncl d n
      map_rel' := fun {a b} hab => (crossWiredGraph_adj_boxVertIncl d n ω a b).mpr hab }
  exact h.map f


theorem inner_reachable_of_crossWiredGraph (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {x y : boxVerts d n}
    (h : (crossWiredGraph d n ω).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
    (wiredGraph (boxGraph d n) (boxBoundary d n) ω).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  
  
  suffices H : ∀ w : boxVerts d (n+1),
      Relation.ReflTransGen (crossWiredGraph d n ω).Adj (boxVertIncl d n x) w →
        ∀ (hw : IsInnerVert d n w),
          (wiredGraph (boxGraph d n) (boxBoundary d n) ω).Reachable x ⟨(w : Site d), hw⟩ by
    have hyinner : IsInnerVert d n (boxVertIncl d n y) := isInnerVert_boxVertIncl d n y
    have := H (boxVertIncl d n y) h hyinner
    
    convert this using 2
  intro w hw hwinner
  induction hw with
  | refl =>
      have : (⟨(boxVertIncl d n x : Site d), hwinner⟩ : boxVerts d n) = x := by
        apply Subtype.ext; rfl
      rw [this]
  | @tail u w hux hadj ih =>
      have huinner : IsInnerVert d n u :=
        crossWiredGraph_reachable_inner d n ω (isInnerVert_boxVertIncl d n x)
          (SimpleGraph.reachable_iff_reflTransGen .. |>.mpr hux)
      have ihu := ih huinner
      
      have hue : u = boxVertIncl d n ⟨(u : Site d), huinner⟩ := by apply Subtype.ext; rfl
      have hwe : w = boxVertIncl d n ⟨(w : Site d), hwinner⟩ := by apply Subtype.ext; rfl
      have hadj' : (crossWiredGraph d n ω).Adj
          (boxVertIncl d n ⟨(u : Site d), huinner⟩)
          (boxVertIncl d n ⟨(w : Site d), hwinner⟩) := by rw [← hue, ← hwe]; exact hadj
      have hstep := (crossWiredGraph_adj_boxVertIncl d n ω
        ⟨(u : Site d), huinner⟩ ⟨(w : Site d), hwinner⟩).mp hadj'
      exact ihu.trans hstep.reachable


end FK
end StatMech
