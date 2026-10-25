/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.Strip.Part2
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.RSW.BoxCrossingUncond
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace RSW

namespace Uncond

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


@[simp] theorem mem_leftReach {ω : ConfigSpace (Sym2 (Site 2))} {x₀ y : Site 2} :
    y ∈ leftReach ω x₀ ↔ Connected 2 ω x₀ y := Iff.rfl

theorem self_mem_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2) :
    x₀ ∈ leftReach ω x₀ := self_mem_cluster ω x₀


theorem noPrimalConn_separated (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2)
    {y₀ : Site 2} (hy₀ : ¬ Connected 2 ω x₀ y₀) :
    ¬ (latticeMinusBarrier (leftReach ω x₀)).Reachable x₀ y₀ :=
  cluster_separated_from_exterior x₀ (by simpa [leftReach, mem_cluster] using hy₀)


theorem noPrimalConn_dualBarrier (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2)
    {x y : Site 2} (hadj : (hypercubicLattice 2).Adj x y)
    (hmem : s(x, y) ∈ bdEdgeSet2 (leftReach ω x₀)) :
    ω s(x, y) = false ∧ dualConfig ω (crossEdge s(x, y)) = true :=
  ⟨cluster_cutEdge_isClosed x₀ hadj hmem, cluster_cutEdge_crosses_dual_open x₀ hadj hmem⟩


theorem escape_crosses_dualBarrier_oddly (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2)
    {y : Site 2} (hy : ¬ Connected 2 ω x₀ y)
    (w : (hypercubicLattice 2).Walk x₀ y) :
    ¬ Even (crossCount (leftReach ω x₀) w) :=
  origin_crossCount_odd x₀ (by simpa [leftReach, mem_cluster] using hy) w


theorem dualBarrierExists (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2)
    (hfin : (cluster 2 ω x₀).Finite) {y₀ : Site 2}
    (w : (hypercubicLattice 2).Walk x₀ y₀) (hy₀ : ¬ Connected 2 ω x₀ y₀) :
    (∃ (u : Site 2) (c : (faceBoundaryGraph (leftReach ω x₀)).Walk u u), c.IsCycle) ∧
      ¬ (latticeMinusBarrier (leftReach ω x₀)).Reachable x₀ y₀ ∧
      ∀ γ : (hypercubicLattice 2).Walk x₀ y₀,
        ¬ Even (crossCount (leftReach ω x₀) γ) := by
  have hzc : y₀ ∉ cluster 2 ω x₀ := by simpa [mem_cluster] using hy₀
  exact cluster_enclosed_with_winding x₀ hfin w hzc


theorem primal_or_dualBarrier (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2)
    (hfin : (cluster 2 ω x₀).Finite) {y₀ : Site 2}
    (w : (hypercubicLattice 2).Walk x₀ y₀) :
    Connected 2 ω x₀ y₀ ∨
      ((∃ (u : Site 2) (c : (faceBoundaryGraph (leftReach ω x₀)).Walk u u), c.IsCycle) ∧
        ¬ (latticeMinusBarrier (leftReach ω x₀)).Reachable x₀ y₀ ∧
        (∀ γ : (hypercubicLattice 2).Walk x₀ y₀,
          ¬ Even (crossCount (leftReach ω x₀) γ))) := by
  rcases Classical.em (Connected 2 ω x₀ y₀) with hconn | hconn
  · exact Or.inl hconn
  · exact Or.inr (dualBarrierExists ω x₀ hfin w hconn)


theorem dualBarrier_isOpenDual (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2)
    {x y : Site 2} (hadj : (hypercubicLattice 2).Adj x y)
    (hmem : s(x, y) ∈ bdEdgeSet2 (leftReach ω x₀)) :
    dualConfig ω (crossEdge s(x, y)) = true :=
  (noPrimalConn_dualBarrier ω x₀ hadj hmem).2


end Uncond
end RSW
end StatMech
