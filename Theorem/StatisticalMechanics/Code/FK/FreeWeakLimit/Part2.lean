/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Instance.StatisticalMechanics.Code.FK.FreeWeakLimit.Part2
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}


theorem outsideOpenGraph_le_fullGraphFree (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    outsideOpenGraph d n ψ ≤ fullGraphFree d n ω ψ := le_sup_right


theorem innerGraphFree_reachable_of_outsideReachable (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {x y : boxVerts d n}
    (h : (outsideOpenGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
    (innerGraphFree d n ω ψ).Reachable x y := by
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl x
  · have hadj : (inducedWiringFree d n ψ).Adj x y := ⟨hxy, h⟩
    exact (le_sup_right (a := openSub (boxGraph d n) ω) hadj).reachable


theorem fullGraphFree_reachable_of_innerGraphFree (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {x y : boxVerts d n} (h : (innerGraphFree d n ω ψ).Reachable x y) :
    (fullGraphFree d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail u w _ hadj ih =>
      refine ih.trans ?_
      rw [SimpleGraph.sup_adj] at hadj
      rcases hadj with hopen | hwire
      · exact ((innerImageGraph_adj_boxVertIncl d n ω u w).mpr hopen).reachable.mono
          le_sup_left
      · exact ((hwire.2.mono (outsideOpenGraph_le_fullGraphFree d n ω ψ)))


theorem innerGraphFree_reachable_of_fullGraphFree (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {x y : boxVerts d n}
    (h : (fullGraphFree d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
    (innerGraphFree d n ω ψ).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  suffices H : ∀ w : boxVerts d (n+1),
      Relation.ReflTransGen (fullGraphFree d n ω ψ).Adj (boxVertIncl d n x) w →
        ∃ x₀ : boxVerts d n, (innerGraphFree d n ω ψ).Reachable x x₀
          ∧ (outsideOpenGraph d n ψ).Reachable (boxVertIncl d n x₀) w by
    obtain ⟨x₀, hKx₀, hout⟩ := H (boxVertIncl d n y) h
    exact hKx₀.trans (innerGraphFree_reachable_of_outsideReachable d n ω ψ hout)
  intro w hw
  induction hw with
  | refl => exact ⟨x, SimpleGraph.Reachable.refl x, SimpleGraph.Reachable.refl _⟩
  | @tail u w _ hadj ih =>
      obtain ⟨x₀, hKx₀, hout⟩ := ih
      rw [SimpleGraph.sup_adj] at hadj
      rcases hadj with himg | hoadj
      · obtain ⟨hu, hw⟩ := innerImageGraph_adj_inner d n ω himg
        obtain ⟨u', rfl⟩ := (isInnerVert_iff_range d n u).mp hu
        obtain ⟨w', rfl⟩ := (isInnerVert_iff_range d n w).mp hw
        have hKu' : (innerGraphFree d n ω ψ).Reachable x₀ u' :=
          innerGraphFree_reachable_of_outsideReachable d n ω ψ hout
        have hstep : (innerGraphFree d n ω ψ).Adj u' w' :=
          le_sup_left (b := inducedWiringFree d n ψ)
            ((innerImageGraph_adj_boxVertIncl d n ω u' w').mp himg)
        have hKw' : (innerGraphFree d n ω ψ).Reachable x w' :=
          ((hKx₀.trans hKu').trans hstep.reachable)
        exact ⟨w', hKw', SimpleGraph.Reachable.refl _⟩
      · exact ⟨x₀, hKx₀, hout.trans hoadj.reachable⟩


theorem fullGraphFree_adj_of_outside (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) {u w : boxVerts d (n+1)}
    (hu : ¬ IsInnerVert d n u) (h : (fullGraphFree d n ω ψ).Adj u w) :
    (outsideOpenGraph d n ψ).Adj u w := by
  rw [SimpleGraph.sup_adj] at h
  rcases h with himg | hout
  · exact absurd (innerImageGraph_adj_inner d n ω himg).1 hu
  · exact hout


end FK
end StatMech
