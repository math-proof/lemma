/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeThermodynamicReduction.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugePerimeterReduction.Part2
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

theorem finiteEventInter_decreasing
    {E I : Type*} {s : Finset I} {A : I -> Set (ConfigSpace E)}
    (hA : forall i, i ∈ s -> IsDecreasing (A i)) :
    IsDecreasing (finiteEventInter s A) := by
  intro omega omega' homega hmem i hi
  exact hA i hi homega (hmem i hi)


theorem fkg_inequality_finite_decreasing_events
    {E I : Type*} [Fintype E] [DecidableEq E]
    {pi : ConfigSpace E -> Real}
    (hpi : 0 <= pi) (hnorm : ∑ omega, pi omega = 1)
    (hlattice : FKGLatticeCondition pi)
    (s : Finset I) (A : I -> Set (ConfigSpace E))
    (hA : forall i, i ∈ s -> IsDecreasing (A i)) :
    (∏ i ∈ s, finiteEventMass pi (A i)) <=
      finiteEventMass pi (finiteEventInter s A) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [finiteEventMass, finiteEventInter, hnorm]
  | @insert a s ha ih =>
      have ha_dec : IsDecreasing (A a) := hA a (Finset.mem_insert_self a s)
      have hs_dec : IsDecreasing (finiteEventInter s A) :=
        finiteEventInter_decreasing (fun i hi => hA i (Finset.mem_insert_of_mem hi))
      have hind := ih (fun i hi => hA i (Finset.mem_insert_of_mem hi))
      have hleft : 0 <= finiteEventMass pi (A a) :=
        finiteEventMass_nonneg hpi (A a)
      have hpair := fkg_inequality_decreasing_events
        hpi hnorm hlattice ha_dec hs_dec
      calc
        (∏ i ∈ insert a s, finiteEventMass pi (A i)) =
            finiteEventMass pi (A a) *
              ∏ i ∈ s, finiteEventMass pi (A i) := by simp [ha]
        _ <= finiteEventMass pi (A a) *
              finiteEventMass pi (finiteEventInter s A) :=
            mul_le_mul_of_nonneg_left hind hleft
        _ <= finiteEventMass pi (A a ∩ finiteEventInter s A) := hpair
        _ = finiteEventMass pi (finiteEventInter (insert a s) A) := by
          congr 1
          ext omega
          simp [finiteEventInter]


end
end StatMech.FrontierA
