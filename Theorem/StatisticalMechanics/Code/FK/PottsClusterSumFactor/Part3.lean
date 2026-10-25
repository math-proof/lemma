/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Def.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part3
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


theorem card_pottsClusterSumFiber_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {q : Nat} [NeZero q] (a b : Fin q) :
    Fintype.card {label : ι -> Fin q // ∑ i, label i = a} =
      Fintype.card {label : ι -> Fin q // ∑ i, label i = b} :=
  Fintype.card_congr (pottsClusterSumFiberEquiv a b)


theorem card_pottsClusterSumFiber_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {q : Nat} [NeZero q] (a : Fin q) :
    q * Fintype.card {label : ι -> Fin q // ∑ i, label i = a} =
      Fintype.card (ι -> Fin q) := by
  let sumMap : (ι -> Fin q) -> Fin q := fun label => ∑ i, label i
  have htotal := Fintype.card_congr (Equiv.sigmaFiberEquiv sumMap)
  rw [Fintype.card_sigma] at htotal
  have hfiber : ∀ b : Fin q,
      Fintype.card {label : ι -> Fin q // sumMap label = b} =
        Fintype.card {label : ι -> Fin q // sumMap label = a} := by
    intro b
    exact card_pottsClusterSumFiber_eq b a
  simp_rw [hfiber] at htotal
  simpa [Fintype.card_fin, Finset.sum_const] using htotal


theorem pottsUniformPi_eq_uniform
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : Nat} [NeZero q] :
    Measure.pi (fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure) =
      (PMF.uniformOfFintype (ι -> Fin q)).toMeasure := by
  apply Measure.ext_of_singleton
  intro label
  rw [Measure.pi_singleton]
  have hinvpow : ∀ n : Nat,
      (q : ENNReal)⁻¹ ^ n = ((q : ENNReal) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ, ih,
          ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top q))
            (Or.inr (by exact_mod_cast (Nat.pos_of_neZero q).ne'))]
  simp [Fintype.card_fin, hinvpow]


theorem pottsUniformPi_sum_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {q : Nat} [NeZero q] (a : Fin q) :
    Measure.pi (fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure)
        {label | ∑ i, label i = a} = (q : ENNReal)⁻¹ := by
  rw [pottsUniformPi_eq_uniform]
  rw [PMF.toMeasure_uniformOfFintype_apply _
    (Set.toFinite {label : ι -> Fin q | ∑ i, label i = a} |>.measurableSet)]
  rw [Fintype.card_subtype]
  have hcard := card_pottsClusterSumFiber_mul (ι := ι) a
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype] at hcard
  rw [Fintype.card_fun, Fintype.card_fin, ENNReal.div_eq_inv_mul]
  have hcast : (q : ENNReal) *
      (↑((Finset.univ.filter fun label : ι -> Fin q => ∑ i, label i = a).card) : ENNReal) =
      (↑(q ^ Fintype.card ι) : ENNReal) := by
    exact_mod_cast hcard
  have hqtop : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  let root : ι := Classical.choice inferInstance
  let witness : ι -> Fin q := pottsLabelTwist root a (fun _ => 0)
  have hwitness : ∑ i, witness i = a := by
    simp [witness, sum_pottsLabelTwist]
  letI : Nonempty {label : ι -> Fin q // ∑ i, label i = a} :=
    ⟨⟨witness, hwitness⟩⟩
  calc
    (↑(q ^ Fintype.card ι) : ENNReal)⁻¹ *
        ↑((Finset.univ.filter fun label : ι -> Fin q => ∑ i, label i = a).card) =
      ((q : ENNReal) *
        ↑((Finset.univ.filter fun label : ι -> Fin q => ∑ i, label i = a).card))⁻¹ *
        ↑((Finset.univ.filter fun label : ι -> Fin q => ∑ i, label i = a).card) := by
      rw [hcast]
    _ = (q : ENNReal)⁻¹ := by
      rw [ENNReal.mul_inv
        (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl hqtop), mul_assoc]
      have hfiber0 :
          (↑((Finset.univ.filter fun label : ι -> Fin q => ∑ i, label i = a).card) :
            ENNReal) ≠ 0 := by
        rw [← Fintype.card_subtype]
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card
          {label : ι -> Fin q // ∑ i, label i = a} ≠ 0)
      rw [ENNReal.inv_mul_cancel hfiber0 (ENNReal.natCast_ne_top _)]
      simp


theorem pottsUniformPi_sum_map
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {q : Nat} [NeZero q] :
    Measure.map (fun label : ι -> Fin q => ∑ i, label i)
        (Measure.pi fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure) =
      (PMF.uniformOfFintype (Fin q)).toMeasure := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply_of_aemeasurable Measurable.of_discrete.aemeasurable
    (Set.toFinite ({a} : Set (Fin q)) |>.measurableSet)]
  change Measure.pi (fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure)
      {label | ∑ i, label i = a} = _
  rw [pottsUniformPi_sum_apply]
  simp


end StatMech.FK
