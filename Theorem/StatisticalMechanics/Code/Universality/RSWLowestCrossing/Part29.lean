/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part28
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_leftPath_arcSeparatingSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    ArcSeparatingSet (rlc_swappedLeftPathSupport gamma)
      (-n) n (-2 * n) 0 := by
  let a0 : ℤ := (gamma.1.1 : Site 2) 1
  let b0 : ℤ := (gamma.1.2.1 : Site 2) 1
  have hstart : crf_swap (gamma.1.1 : Site 2) = ![a0, -2 * n] := by
    have hs := gamma.1.1.2
    rw [mem_leftSide] at hs
    ext i
    fin_cases i <;> simp [a0, hs.2]
  have hend : crf_swap (gamma.1.2.1 : Site 2) = ![b0, 0] := by
    have he := gamma.1.2.1.2
    rw [mem_rightSide] at he
    ext i
    fin_cases i <;> simp [b0, he.2]
  let V : (hypercubicLattice 2).Walk ![a0, -2 * n] ![b0, 0] :=
    (rlc_swappedLeftPathWalk gamma).copy hstart hend
  have hs := gamma.1.1.2
  have he := gamma.1.2.1.2
  rw [mem_leftSide, mem_rect] at hs
  rw [mem_rightSide, mem_rect] at he
  have hVbox : ∀ p ∈ V.support, p ∈ rect (-n) n (-2 * n) 0 := by
    intro p hp
    dsimp only [V] at hp
    rw [SimpleGraph.Walk.support_copy] at hp
    change p ∈ (SimpleGraph.Walk.map (rlc_swapLeftInducedHom n)
      gamma.1.2.2.1).support at hp
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact (crf_mem_rect_swap (-2 * n) 0 (-n) n (z : Site 2)).mp z.2
  have hVP : ∀ p ∈ V.support,
      p ∈ rlc_swappedLeftPathSupport gamma := by
    intro p hp
    dsimp only [V] at hp
    rw [SimpleGraph.Walk.support_copy] at hp
    change p ∈ (SimpleGraph.Walk.map (rlc_swapLeftInducedHom n)
      gamma.1.2.2.1).support at hp
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact ⟨z, hz, rfl⟩
  exact jec_arcSeparatingSet (-n) n (-2 * n) 0 a0 b0
    (by omega) (by omega)
    hs.1.2.2.1 hs.1.2.2.2 he.1.2.2.1 he.1.2.2.2
    V hVbox _ hVP

end Universality
end StatMech
