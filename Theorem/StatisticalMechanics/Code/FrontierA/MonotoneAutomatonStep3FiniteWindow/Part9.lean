/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part8
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem measurableSet_pairStep3DistanceAt (root : Site d) (D : ℕ) :
    MeasurableSet (pairStep3DistanceAt root D) := by
  have hatLeast : MeasurableSet {omega : PairSiteConfig d |
      ∀ y ∈ pairHighCluster omega root,
      ∀ x ∈ pairLowInfiniteVertices omega, D ≤ l1dist d y x} := by
    have heq : {omega : PairSiteConfig d |
        ∀ y ∈ pairHighCluster omega root,
        ∀ x ∈ pairLowInfiniteVertices omega, D ≤ l1dist d y x} =
        ⋂ y : Site d, ⋂ x : Site d,
          if D ≤ l1dist d y x then Set.univ else
            {omega | y ∈ pairHighCluster omega root}ᶜ ∪
              {omega | x ∈ pairLowInfiniteVertices omega}ᶜ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h y x
        split_ifs with hD
        · trivial
        · by_cases hy : y ∈ pairHighCluster omega root
          · exact Or.inr (fun hx => hD (h y hy x hx))
          · exact Or.inl hy
      · intro h y hy x hx
        have := h y x
        split_ifs at this with hD
        · exact hD
        · exact (this.elim (fun hny => hny hy) (fun hnx => hnx hx)).elim
    rw [heq]
    exact MeasurableSet.iInter fun y => MeasurableSet.iInter fun x => by
      split_ifs
      · exact MeasurableSet.univ
      · exact (measurableSet_pairHighConnected root y).compl.union
          (measurableSet_pairLowInfinite x).compl
  have hattained : MeasurableSet {omega : PairSiteConfig d |
      ∃ y ∈ pairHighCluster omega root,
      ∃ x ∈ pairLowInfiniteVertices omega, l1dist d y x = D} := by
    have heq : {omega : PairSiteConfig d |
        ∃ y ∈ pairHighCluster omega root,
        ∃ x ∈ pairLowInfiniteVertices omega, l1dist d y x = D} =
        ⋃ y : Site d, ⋃ x : Site d,
          if l1dist d y x = D then
            {omega | y ∈ pairHighCluster omega root} ∩
              {omega | x ∈ pairLowInfiniteVertices omega}
          else ∅ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      aesop
    rw [heq]
    exact MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun x => by
      split_ifs
      · exact (measurableSet_pairHighConnected root y).inter
          (measurableSet_pairLowInfinite x)
      · exact MeasurableSet.empty
  exact ((measurableSet_pairStep3CoreAt root).inter hatLeast).inter hattained

theorem pairStep3CoreAt_eq_iUnion_distance (root : Site d) :
    pairStep3CoreAt root = ⋃ D : ℕ, pairStep3DistanceAt root D := by
  ext omega
  constructor
  · intro hcore
    have hnearest : (pairNearestHighSet omega root).Nonempty :=
      hcore.2.nonempty
    obtain ⟨y, hy⟩ := hnearest
    rcases hy with ⟨hyCluster, x, hxLow, hxy⟩
    apply Set.mem_iUnion.mpr
    refine ⟨l1dist d y x, ?_⟩
    refine ⟨⟨hcore, ?_⟩, y, hyCluster, x, hxLow, rfl⟩
    intro z hz a ha
    rw [hxy]
    exact Nat.sInf_le ⟨z, hz, a, ha, rfl⟩
  · intro h
    obtain ⟨D, hD⟩ := Set.mem_iUnion.mp h
    exact hD.1.1

end StatMech.FrontierA
