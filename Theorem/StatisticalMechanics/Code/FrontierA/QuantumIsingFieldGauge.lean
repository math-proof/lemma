/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFieldGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteHamiltonian.Part4
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingFieldGauge
open Matrix
open scoped Norms.Operator


namespace StatMech.FrontierA

@[simp] theorem quantumIsingFieldGaugeSign_sq {L : Nat}
    (sigma : QuantumIsingChainConfig L) :
    quantumIsingFieldGaugeSign sigma * quantumIsingFieldGaugeSign sigma = 1 := by
  unfold quantumIsingFieldGaugeSign
  rw [← Finset.prod_mul_distrib]
  simp [quantumIsingSpinSign_mul_self]

theorem quantumIsingSpinSign_eq_neg_of_ne {s t : Bool} (hst : s ≠ t) :
    quantumIsingSpinSign s = -quantumIsingSpinSign t := by
  cases s <;> cases t <;> simp_all [quantumIsingSpinSign]


theorem quantumIsingFieldGaugeSign_eq_neg_of_disagreementCount_eq_one
    {L : Nat} (sigma tau : QuantumIsingChainConfig L)
    (hcount : quantumIsingDisagreementCount sigma tau = 1) :
    quantumIsingFieldGaugeSign sigma = -quantumIsingFieldGaugeSign tau := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcount
  have hdiff : sigma i ≠ tau i := by
    have : i ∈ quantumIsingDisagreementSet sigma tau := by simp [hi]
    simpa [quantumIsingDisagreementSet] using this
  have hout (j : Fin L) (hji : j ≠ i) : sigma j = tau j := by
    by_contra hne
    have hj : j ∈ quantumIsingDisagreementSet sigma tau := by
      simp [quantumIsingDisagreementSet, hne]
    rw [hi] at hj
    exact hji (Finset.mem_singleton.mp hj)
  unfold quantumIsingFieldGaugeSign
  rw [← Finset.univ.mul_prod_erase
      (fun j => quantumIsingSpinSign (sigma j)) (Finset.mem_univ i),
    ← Finset.univ.mul_prod_erase
      (fun j => quantumIsingSpinSign (tau j)) (Finset.mem_univ i)]
  have herase :
      ∏ j ∈ Finset.univ.erase i, quantumIsingSpinSign (sigma j) =
        ∏ j ∈ Finset.univ.erase i, quantumIsingSpinSign (tau j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hout j (Finset.ne_of_mem_erase hj)]
  rw [herase, quantumIsingSpinSign_eq_neg_of_ne hdiff]
  ring


end StatMech.FrontierA
