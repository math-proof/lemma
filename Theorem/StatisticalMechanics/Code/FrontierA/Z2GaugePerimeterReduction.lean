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
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugePerimeterReduction
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

theorem finiteEventMass_nonneg {E : Type*} [Fintype E] [DecidableEq E]
    {pi : ConfigSpace E -> Real} (hpi : 0 <= pi)
    (A : Set (ConfigSpace E)) :
    0 <= finiteEventMass pi A := by
  unfold finiteEventMass
  apply Finset.sum_nonneg
  intro omega _
  exact mul_nonneg (hpi omega) (indicator_nonneg' A omega)


theorem fkg_inequality_decreasing_events
    {E : Type*} [Fintype E] [DecidableEq E]
    {pi : ConfigSpace E -> Real}
    (hpi : 0 <= pi) (hnorm : ∑ omega, pi omega = 1)
    (hlattice : FKGLatticeCondition pi)
    {A B : Set (ConfigSpace E)}
    (hA : IsDecreasing A) (hB : IsDecreasing B) :
    finiteEventMass pi A * finiteEventMass pi B <=
      finiteEventMass pi (A ∩ B) := by
  let f : ConfigSpace E -> Real :=
    A.indicator (fun _ => (1 : Real))
  let g : ConfigSpace E -> Real :=
    B.indicator (fun _ => (1 : Real))
  have hfanti : Antitone f := by
    intro omega omega' homega
    by_cases hmem : omega ∈ A
    · by_cases hmem' : omega' ∈ A <;>
        simp [f, hmem, hmem']
    · have hmem' : omega' ∉ A := fun homega' => hmem (hA homega homega')
      simp [f, hmem, hmem']
  have hganti : Antitone g := by
    intro omega omega' homega
    by_cases hmem : omega ∈ B
    · by_cases hmem' : omega' ∈ B <;>
        simp [g, hmem, hmem']
    · have hmem' : omega' ∉ B := fun homega' => hmem (hB homega homega')
      simp [g, hmem, hmem']
  have hfmono : Monotone (fun omega => -f omega) := by
    intro omega omega' homega
    exact neg_le_neg (hfanti homega)
  have hgmono : Monotone (fun omega => -g omega) := by
    intro omega omega' homega
    exact neg_le_neg (hganti homega)
  have h := fkg_inequality hpi hnorm hlattice hfmono hgmono
  have hAB : (A ∩ B).indicator (fun _ => (1 : Real)) =
      fun omega => f omega * g omega := by
    funext omega
    by_cases ha : omega ∈ A <;> by_cases hb : omega ∈ B <;>
      simp [f, g, Set.indicator, ha, hb]
  unfold finiteEventMass
  rw [hAB]
  simpa only [mul_neg, Finset.sum_neg_distrib, neg_mul, neg_neg] using h


end
end StatMech.FrontierA
