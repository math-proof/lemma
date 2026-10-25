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
import Def.StatisticalMechanics.Code.FK.InducedBC.Part6
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem outsideOnly_self_not_inner (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {u : boxVerts d (n+1)} (hu : OutsideOnly d n ψ u) : ¬ IsInnerVert d n u :=
  hu u (SimpleGraph.Reachable.refl u)


theorem outsideOnly_of_reachable (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {u v : boxVerts d (n+1)} (hu : OutsideOnly d n ψ u)
    (h : (outsideGraph d n ψ).Reachable u v) : OutsideOnly d n ψ v :=
  fun w hw => hu w (h.trans hw)


theorem outsideGraph_reachable_of_fullGraph_outsideOnly (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {u w : boxVerts d (n+1)} (hu : OutsideOnly d n ψ u)
    (h : (fullGraph d n ω ψ).Reachable u w) :
    (outsideGraph d n ψ).Reachable u w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail a b hua hadj ih =>
      have ha_out : (outsideGraph d n ψ).Reachable u a := ih
      have ha_not_inner : ¬ IsInnerVert d n a := hu a ha_out
      exact ha_out.trans (fullGraph_adj_of_outside d n ω ψ ha_not_inner hadj).reachable


end FK
end StatMech
