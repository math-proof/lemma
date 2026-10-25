/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3Bridge.Part4
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part2
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem measurableSet_pairStep3CoreAt (x : Site d) :
    MeasurableSet (pairStep3CoreAt x) := by
  exact (measurableSet_pairDisjointInfiniteHighAt x).inter
    (measurableSet_pairNearestHighSet_finite x).compl


theorem pairDisjointInfiniteHighAt_shift (g : Multiplicative (Site d))
    (omega : PairSiteConfig d) (x : Site d) :
    StatMech.ConfigSpace.shift g omega ∈
        pairDisjointInfiniteHighAt (g • x) ↔
      omega ∈ pairDisjointInfiniteHighAt x := by
  unfold pairDisjointInfiniteHighAt
  simp only [Set.mem_setOf_eq]
  rw [pairHighCluster_shift, pairLowInfiniteVertices_shift]
  simp only [translateSiteSet]
  have hinj : Function.Injective
      (fun z : Site d => Multiplicative.toAdd g + z) :=
    add_right_injective _
  rw [Set.infinite_image_iff (Set.injOn_of_injective hinj),
    ← Set.image_inter hinj, Set.image_nonempty]


theorem pairDisjointInfiniteHighAt_measure_zero_of_origin
    (nu : Measure (PairSiteConfig d)) [IsProbabilityMeasure nu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) nu)
    (hzero : nu (pairDisjointInfiniteHighAt (0 : Site d)) = 0)
    (x : Site d) :
    nu (pairDisjointInfiniteHighAt x) = 0 := by
  let g : Multiplicative (Site d) := Multiplicative.ofAdd x
  have hg0 : g • (0 : Site d) = x := by
    change x + 0 = x
    simp
  have hpre :
      (StatMech.ConfigSpace.shift g : PairSiteConfig d → PairSiteConfig d) ⁻¹'
          pairDisjointInfiniteHighAt x =
        pairDisjointInfiniteHighAt (0 : Site d) := by
    ext omega
    change StatMech.ConfigSpace.shift g omega ∈
        pairDisjointInfiniteHighAt x ↔
      omega ∈ pairDisjointInfiniteHighAt (0 : Site d)
    rw [← hg0]
    exact pairDisjointInfiniteHighAt_shift g omega 0
  calc
    nu (pairDisjointInfiniteHighAt x) =
        nu ((StatMech.ConfigSpace.shift g :
          PairSiteConfig d → PairSiteConfig d) ⁻¹'
            pairDisjointInfiniteHighAt x) :=
      (hinv.measure_preimage g
        (measurableSet_pairDisjointInfiniteHighAt x)).symm
    _ = nu (pairDisjointInfiniteHighAt (0 : Site d)) := by rw [hpre]
    _ = 0 := hzero


end StatMech.FrontierA
