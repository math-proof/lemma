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
import Def.StatisticalMechanics.Code.FK.FreeWeakLimit.Part2
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


theorem outsideOnlyFree_self_not_inner (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) {u : boxVerts d (n+1)}
    (hu : OutsideOnlyFree d n ψ u) : ¬ IsInnerVert d n u :=
  hu u (SimpleGraph.Reachable.refl u)

theorem outsideOnlyFree_of_reachable (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {u v : boxVerts d (n+1)} (hu : OutsideOnlyFree d n ψ u)
    (h : (outsideOpenGraph d n ψ).Reachable u v) : OutsideOnlyFree d n ψ v :=
  fun w hw => hu w (h.trans hw)


theorem outsideOpenGraph_reachable_of_fullGraphFree_outsideOnly (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {u w : boxVerts d (n+1)} (hu : OutsideOnlyFree d n ψ u)
    (h : (fullGraphFree d n ω ψ).Reachable u w) :
    (outsideOpenGraph d n ψ).Reachable u w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail a b hua hadj ih =>
      have ha_out : (outsideOpenGraph d n ψ).Reachable u a := ih
      have ha_not_inner : ¬ IsInnerVert d n a := hu a ha_out
      exact ha_out.trans (fullGraphFree_adj_of_outside d n ω ψ ha_not_inner hadj).reachable


end FK
end StatMech
