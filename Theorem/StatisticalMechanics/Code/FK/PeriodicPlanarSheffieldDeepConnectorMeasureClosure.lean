/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorMeasureClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorCage
open Filter MeasureTheory Set


namespace StatMech.FK.PeriodicPlanar

theorem measure_eq_zero_of_disjoint_measureReal_tendsto_one
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Nat → Set X) (B : Set X) (hB : MeasurableSet B)
    (hdisjoint : ∀ n, Disjoint (A n) B)
    (hA : Tendsto (fun n => mu.real (A n)) atTop (nhds 1)) :
    mu B = 0 := by
  have hsum (n : Nat) : mu.real (A n) + mu.real B ≤ 1 := by
    have hinter : A n ∩ B = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp (hdisjoint n)
    have hadd := measureReal_union_add_inter (μ := mu) hB (s := A n)
    rw [hinter] at hadd
    simp only [measureReal_empty, add_zero] at hadd
    have hunion : mu.real (A n ∪ B) ≤ 1 := measureReal_le_one
    linarith
  have hadd : Tendsto (fun n => mu.real (A n) + mu.real B)
      atTop (nhds (1 + mu.real B)) :=
    hA.add tendsto_const_nhds
  have hlimit : 1 + mu.real B ≤ 1 :=
    le_of_tendsto hadd (Eventually.of_forall hsum)
  have hreal : mu.real B = 0 := by
    exact le_antisymm (by linarith) measureReal_nonneg
  exact ((ENNReal.toReal_eq_zero_iff (mu B)).mp hreal).resolve_right
    (measure_ne_top mu B)

end StatMech.FK.PeriodicPlanar
