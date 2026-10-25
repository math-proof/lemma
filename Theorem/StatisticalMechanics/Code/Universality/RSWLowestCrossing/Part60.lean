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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part59
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_extremalPairCandidate_dependsOn {n : ℤ}
    (pair : RlcDiagonalPathPair n) :
    DependsOn ((rlc_extremalPairCandidate pair).indicator (fun _ => (1 : ℝ)))
      (rlc_extremalPairCandidateEdges pair : Set (Sym2 (Site 2))) := by
  simpa only [rlc_extremalPairCandidate, rlc_extremalPairCandidateEdges,
    Finset.coe_union] using
      dependsOn_inter (rlc_rightLowestCandidate_dependsOn pair.1)
        (rlc_leftHighestCandidate_dependsOn pair.2)

theorem rlc_extremalPairCandidate_subset_pathPairOpen {n : ℤ}
    (pair : RlcDiagonalPathPair n) :
    rlc_extremalPairCandidate pair ⊆ rlc_pathPairOpen pair := by
  rintro omega ⟨hright, hleft⟩
  exact ⟨hright.1, hleft.1⟩


theorem rlc_iUnion_extremalPairCandidate (n : ℤ) :
    (⋃ pair : RlcDiagonalPathPair n, rlc_extremalPairCandidate pair) =
      rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
  ext omega
  constructor
  · intro h
    obtain ⟨pair, hright, hleft⟩ := Set.mem_iUnion.mp h
    constructor
    · rw [← rlc_iUnion_rightLowestCandidate]
      exact Set.mem_iUnion.mpr ⟨pair.1, hright⟩
    · rw [← rlc_iUnion_leftHighestCandidate]
      exact Set.mem_iUnion.mpr ⟨pair.2, hleft⟩
  · rintro ⟨hright, hleft⟩
    rw [← rlc_iUnion_rightLowestCandidate] at hright
    rw [← rlc_iUnion_leftHighestCandidate] at hleft
    obtain ⟨gamma, hgamma⟩ := Set.mem_iUnion.mp hright
    obtain ⟨delta, hdelta⟩ := Set.mem_iUnion.mp hleft
    exact Set.mem_iUnion.mpr ⟨(gamma, delta), hgamma, hdelta⟩

theorem rlc_rightLowestCandidate_not_open_of_below {n : ℤ}
    {gamma delta : RlcRightDiagonalPath n}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_rightLowestCandidate gamma)
    (hbelow : rlc_rightPathBelow delta gamma) :
    omega ∉ rlc_pathOpen delta.1 := by
  intro hdelta
  apply hgamma.2
  exact Set.mem_iUnion.mpr ⟨delta, by simp [hbelow, hdelta]⟩

theorem rlc_leftHighestCandidate_not_open_of_above {n : ℤ}
    {gamma delta : RlcLeftDiagonalPath n}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_leftHighestCandidate gamma)
    (habove : rlc_leftPathAbove delta gamma) :
    omega ∉ rlc_pathOpen delta.1 := by
  intro hdelta
  apply hgamma.2
  exact Set.mem_iUnion.mpr ⟨delta, by simp [habove, hdelta]⟩


end Universality
end StatMech
