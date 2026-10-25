/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestConclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestMeasurable.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestConclusion.Part2
open MeasureTheory Set


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem pairHasFiniteNearestHighCluster_subset :
    pairHasFiniteNearestHighCluster (d := d) ⊆
      ⋃ y : Site d, pairFiniteNearestAt y := by
  intro omega homega
  rcases homega with ⟨hlow, x, hhigh, hfin⟩
  obtain ⟨y, hy⟩ := pairNearestHighSet_nonempty omega x hlow
  have hyCluster : y ∈ pairHighCluster omega x :=
    pairNearestHighSet_subset_cluster omega x hy
  have hcluster : pairHighCluster omega y = pairHighCluster omega x :=
    pairHighCluster_eq_of_mem hyCluster
  have hnearest : pairNearestHighSet omega y = pairNearestHighSet omega x :=
    pairNearestHighSet_eq_of_mem hyCluster
  rw [Set.mem_iUnion]
  refine ⟨y, ?_⟩
  exact ⟨hcluster.symm ▸ hhigh, hlow, hnearest.symm ▸ hfin,
    hnearest.symm ▸ hy⟩


theorem pairHasFiniteNearestHighCluster_measure_zero
    (mu : Measure (PairSiteConfig d)) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
    mu (pairHasFiniteNearestHighCluster (d := d)) = 0 := by
  apply measure_mono_null pairHasFiniteNearestHighCluster_subset
  apply measure_iUnion_null
  exact pairFiniteNearestAt_measure_zero mu hinv


theorem interpolatedHighPair_no_finite_nearest
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hinv : IsTripleFieldTranslationInvariant mu) :
    (interpolatedHighPairLaw T mu)
      (pairHasFiniteNearestHighCluster (d := d)) = 0 := by
  letI : IsProbabilityMeasure (interpolatedHighPairLaw T mu) := by
    unfold interpolatedHighPairLaw
    exact inferInstance
  exact pairHasFiniteNearestHighCluster_measure_zero
    (interpolatedHighPairLaw T mu)
    (interpolatedHighPairLaw_isTranslationInvariant T mu hinv)

end StatMech.FrontierA
