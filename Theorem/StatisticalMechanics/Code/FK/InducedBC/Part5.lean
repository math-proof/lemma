/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean -/

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
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Instance.StatisticalMechanics.Code.FK.InducedBC.Part5
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem outsideGraph_le_fullGraph (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    outsideGraph d n ψ ≤ fullGraph d n ω ψ := le_sup_right


theorem innerImageGraph_adj_inner (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {u v : boxVerts d (n+1)} (h : (innerImageGraph d n ω).Adj u v) :
    IsInnerVert d n u ∧ IsInnerVert d n v := by
  obtain ⟨_, _, hr⟩ := h
  obtain ⟨e, he⟩ := hr
  refine Sym2.inductionOn e (fun a b hab => ?_) he
  rw [innerEdge, Sym2.map_mk, Sym2.eq_iff] at hab
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; exact ⟨isInnerVert_boxVertIncl d n a, isInnerVert_boxVertIncl d n b⟩
  · subst h1; subst h2; exact ⟨isInnerVert_boxVertIncl d n b, isInnerVert_boxVertIncl d n a⟩


theorem innerImageGraph_adj_boxVertIncl (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (x y : boxVerts d n) :
    (innerImageGraph d n ω).Adj (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (openSub (boxGraph d n) ω).Adj x y := by
  have he : s(boxVertIncl d n x, boxVertIncl d n y) = innerEdge d n s(x, y) := by
    rw [innerEdge, Sym2.map_mk]
  constructor
  · rintro ⟨hadj, hopen, _⟩
    refine ⟨(boxGraph_adj_boxVertIncl d n x y).mp hadj, ?_⟩
    rw [he, psiExt_innerEdge] at hopen; exact hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨(boxGraph_adj_boxVertIncl d n x y).mpr hadj, ?_, ⟨s(x, y), he.symm⟩⟩
    rw [he, psiExt_innerEdge]; exact hopen


theorem innerGraph_reachable_of_outsideReachable (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {x y : boxVerts d n}
    (h : (outsideGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
    (innerGraph d n ω ψ).Reachable x y := by
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl x
  · have hadj : (inducedWiring d n ψ).Adj x y := ⟨hxy, h⟩
    exact (le_sup_right (a := openSub (boxGraph d n) ω) hadj).reachable


theorem fullGraph_reachable_of_innerGraph (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {x y : boxVerts d n} (h : (innerGraph d n ω ψ).Reachable x y) :
    (fullGraph d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail u w _ hadj ih =>
      refine ih.trans ?_
      rw [SimpleGraph.sup_adj] at hadj
      rcases hadj with hopen | hwire
      · exact ((innerImageGraph_adj_boxVertIncl d n ω u w).mpr hopen).reachable.mono
          le_sup_left
      · exact ((hwire.2.mono (outsideGraph_le_fullGraph d n ω ψ)))


theorem innerGraph_reachable_of_fullGraph (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {x y : boxVerts d n}
    (h : (fullGraph d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
    (innerGraph d n ω ψ).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  
  suffices H : ∀ w : boxVerts d (n+1),
      Relation.ReflTransGen (fullGraph d n ω ψ).Adj (boxVertIncl d n x) w →
        ∃ x₀ : boxVerts d n, (innerGraph d n ω ψ).Reachable x x₀
          ∧ (outsideGraph d n ψ).Reachable (boxVertIncl d n x₀) w by
    obtain ⟨x₀, hKx₀, hout⟩ := H (boxVertIncl d n y) h
    exact hKx₀.trans (innerGraph_reachable_of_outsideReachable d n ω ψ hout)
  intro w hw
  induction hw with
  | refl => exact ⟨x, SimpleGraph.Reachable.refl x, SimpleGraph.Reachable.refl _⟩
  | @tail u w _ hadj ih =>
      obtain ⟨x₀, hKx₀, hout⟩ := ih
      rw [SimpleGraph.sup_adj] at hadj
      rcases hadj with himg | hoadj
      · 
        obtain ⟨hu, hw⟩ := innerImageGraph_adj_inner d n ω himg
        obtain ⟨u', rfl⟩ := (isInnerVert_iff_range d n u).mp hu
        obtain ⟨w', rfl⟩ := (isInnerVert_iff_range d n w).mp hw
        
        have hKu' : (innerGraph d n ω ψ).Reachable x₀ u' :=
          innerGraph_reachable_of_outsideReachable d n ω ψ hout
        have hstep : (innerGraph d n ω ψ).Adj u' w' :=
          le_sup_left (b := inducedWiring d n ψ) ((innerImageGraph_adj_boxVertIncl d n ω u' w').mp himg)
        have hKw' : (innerGraph d n ω ψ).Reachable x w' :=
          ((hKx₀.trans hKu').trans hstep.reachable)
        exact ⟨w', hKw', SimpleGraph.Reachable.refl _⟩
      · 
        exact ⟨x₀, hKx₀, hout.trans hoadj.reachable⟩


theorem fullGraph_reachable_boxVertIncl (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (x y : boxVerts d n) :
    (fullGraph d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (innerGraph d n ω ψ).Reachable x y :=
  ⟨innerGraph_reachable_of_fullGraph d n ω ψ, fullGraph_reachable_of_innerGraph d n ω ψ⟩


theorem fullGraph_adj_of_outside (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) {u w : boxVerts d (n+1)}
    (hu : ¬ IsInnerVert d n u) (h : (fullGraph d n ω ψ).Adj u w) :
    (outsideGraph d n ψ).Adj u w := by
  rw [SimpleGraph.sup_adj] at h
  rcases h with himg | hout
  · exact absurd (innerImageGraph_adj_inner d n ω himg).1 hu
  · exact hout


end FK
end StatMech
