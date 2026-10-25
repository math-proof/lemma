/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part2


namespace StatMech.FrontierA

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem cylinderMin_le_self (f : ConfigSpace E → ℝ) (K : Set E)
    (omega : ConfigSpace E) : cylinderMin f K omega ≤ f omega := by
  classical
  exact Finset.inf'_le _ (mem_agreementFiber.mpr (agreeOn_refl K omega))


theorem cylinderMin_nonneg {f : ConfigSpace E → ℝ} (hf : ∀ omega, 0 ≤ f omega)
    (K : Set E) (omega : ConfigSpace E) : 0 ≤ cylinderMin f K omega := by
  classical
  apply Finset.le_inf'
  intro eta _
  exact hf eta


theorem cylinderMin_mono {f g : ConfigSpace E → ℝ} (hfg : ∀ omega, f omega ≤ g omega)
    (K : Set E) (omega : ConfigSpace E) :
    cylinderMin f K omega ≤ cylinderMin g K omega := by
  classical
  apply Finset.le_inf'
  intro eta heta
  exact le_trans (Finset.inf'_le _ heta) (hfg eta)


theorem agreementFiber_eq_of_agreeOn {K : Set E} {omega omega' : ConfigSpace E}
    (h : agreeOn K omega omega') : agreementFiber K omega = agreementFiber K omega' := by
  classical
  ext eta
  simp only [mem_agreementFiber]
  constructor
  · intro heta e he
    exact (heta e he).trans (h e he).symm
  · intro heta e he
    exact (heta e he).trans (h e he)


theorem cylinderMin_eq_of_agreeOn (f : ConfigSpace E → ℝ) {K : Set E}
    {omega omega' : ConfigSpace E} (h : agreeOn K omega omega') :
    cylinderMin f K omega = cylinderMin f K omega' := by
  classical
  simp only [cylinderMin, agreementFiber_eq_of_agreeOn h]


end StatMech.FrontierA
