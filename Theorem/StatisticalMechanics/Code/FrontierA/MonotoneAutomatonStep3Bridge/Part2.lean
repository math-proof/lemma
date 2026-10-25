/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonCoarseTrifurcationGeneral.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSingleSiteStability.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MultivaluedMap
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3Bridge
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


theorem measurableSet_pairHasFiniteNearestInfiniteHighCluster :
    MeasurableSet (pairHasFiniteNearestInfiniteHighCluster (d := d)) := by
  have heq : pairHasFiniteNearestInfiniteHighCluster (d := d) =
      ⋃ x : Site d, {omega | (pairHighCluster omega x).Infinite} ∩
        {omega | (pairNearestHighSet omega x).Finite} := by
    ext omega
    simp [pairHasFiniteNearestInfiniteHighCluster]
  rw [heq]
  exact MeasurableSet.iUnion fun x =>
    (measurableSet_pairHighInfinite x).inter
      (measurableSet_pairNearestHighSet_finite x)


theorem interpolatedHighPair_lowInfinite_nonempty_of_lowOutput
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
    (interpolatedHighPairLaw T mu)
      {omega | (pairLowInfiniteVertices omega).Nonempty} = 1 := by
  have hsub : {q : FieldTriple d |
      1 ≤ numInfiniteClusters d (siteToBond (T q.1))} ⊆
      (interpolatedHighPair T) ⁻¹'
        {omega | (pairLowInfiniteVertices omega).Nonempty} := by
    intro q hq
    have haux := one_le_numInfiniteClusters_siteToBond_mono
      (automatonLow_le_interpolated T q) hq
    obtain ⟨x, hx⟩ :=
      (one_le_numInfiniteClusters_siteToBond_iff
        (interpolatedSite T q)).mp haux
    exact pairLowInfiniteVertices_nonempty (interpolatedHighPair T q) hx
  have hfull : mu ((interpolatedHighPair T) ⁻¹'
      {omega | (pairLowInfiniteVertices omega).Nonempty}) = 1 := by
    apply le_antisymm prob_le_one
    exact hlow ▸ measure_mono hsub
  rw [interpolatedHighPairLaw, Measure.map_apply
    (measurable_interpolatedHighPair T)
    measurableSet_pairLowInfiniteVertices_nonempty]
  exact hfull


theorem interpolatedHighPair_finiteNearestInfiniteHighCluster_measure_zero
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hinv : IsTripleFieldTranslationInvariant mu)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
    (interpolatedHighPairLaw T mu)
      (pairHasFiniteNearestInfiniteHighCluster (d := d)) = 0 := by
  letI : IsProbabilityMeasure (interpolatedHighPairLaw T mu) := by
    unfold interpolatedHighPairLaw
    exact inferInstance
  let lowNonempty : Set (PairSiteConfig d) :=
    {omega | (pairLowInfiniteVertices omega).Nonempty}
  have hlowFull : (interpolatedHighPairLaw T mu) lowNonempty = 1 :=
    interpolatedHighPair_lowInfinite_nonempty_of_lowOutput T mu hlow
  have hlowCompl : (interpolatedHighPairLaw T mu) lowNonemptyᶜ = 0 := by
    rw [measure_compl measurableSet_pairLowInfiniteVertices_nonempty
      (measure_ne_top _ _), hlowFull]
    simp
  have hbad : (interpolatedHighPairLaw T mu)
      (pairHasFiniteNearestHighCluster (d := d)) = 0 :=
    interpolatedHighPair_no_finite_nearest T mu hinv
  apply measure_mono_null (t :=
    pairHasFiniteNearestHighCluster (d := d) ∪ lowNonemptyᶜ)
  · intro omega homega
    by_cases hlowOmega : omega ∈ lowNonempty
    · left
      exact ⟨hlowOmega, homega⟩
    · exact Or.inr hlowOmega
  · exact measure_union_null hbad hlowCompl


end StatMech.FrontierA
