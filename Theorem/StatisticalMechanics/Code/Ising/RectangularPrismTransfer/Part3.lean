/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.CylinderPathExpansion
import Theorem.StatisticalMechanics.Code.Ising.CenterMarkedPath.Part2
import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferCenterObservable
import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part3
import Def.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part3
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

theorem rectangularPrismSpin_layer
    {m n h : Nat} (sigma : RectangularPrismConfig m n h)
    (x : Fin m) (y : Fin n) (z : Fin (2 * h + 1)) :
    rectangularPrismSpin sigma x y z =
      spin (rectangularPrismLayer sigma z) (x, y) := rfl

theorem rectangularPrismInternalInteraction_eq_layers
    {m n h : Nat} (sigma : RectangularPrismConfig m n h) :
    rectangularPrismInternalInteraction sigma =
      (∑ z : Fin (2 * h + 1),
        rectangularLayerInternalInteraction (rectangularPrismLayer sigma z)) +
      ∑ z : Fin (2 * h), ∑ p : Fin m × Fin n,
        spin (rectangularPrismLayer sigma z.castSucc) p *
          spin (rectangularPrismLayer sigma z.succ) p := by
  unfold rectangularPrismInternalInteraction
    rectangularLayerInternalInteraction rectangularPrismSpin
  rw [Finset.sum_add_distrib]
  rw [sum_comm_three (fun (x : Fin (m - 1)) (y : Fin n)
    (z : Fin (2 * h + 1)) =>
      spin sigma ⟨⟨x.val, by omega⟩, y, z⟩ *
        spin sigma ⟨⟨x.val + 1, by omega⟩, y, z⟩)]
  rw [sum_comm_three (fun (x : Fin m) (y : Fin (n - 1))
    (z : Fin (2 * h + 1)) =>
      spin sigma ⟨x, ⟨y.val, by omega⟩, z⟩ *
        spin sigma ⟨x, ⟨y.val + 1, by omega⟩, z⟩)]
  rw [sum_comm_three (fun (x : Fin m) (y : Fin n) (z : Fin (2 * h)) =>
    spin sigma ⟨x, y, ⟨z.val, by omega⟩⟩ *
      spin sigma ⟨x, y, ⟨z.val + 1, by omega⟩⟩)]
  simp_rw [Fintype.sum_prod_type]
  rfl

theorem rectangularPrismBoundaryDegree_split
    {m n h : Nat} (x : Fin m) (y : Fin n) (z : Fin (2 * h + 1)) :
    rectangularPrismBoundaryDegree ⟨x, y, z⟩ =
      rectangularLayerBoundaryDegree (x, y) +
        (if z.val = 0 then 1 else 0) +
        (if z.val + 1 = 2 * h + 1 then 1 else 0) := by
  rfl

theorem rectangularPrismPlusBoundaryInteraction_eq_layers
    {m n h : Nat} (sigma : RectangularPrismConfig m n h) :
    rectangularPrismPlusBoundaryInteraction sigma =
      (∑ z : Fin (2 * h + 1), ∑ p : Fin m × Fin n,
        rectangularLayerBoundaryDegree p *
          spin (rectangularPrismLayer sigma z) p) +
      (∑ p : Fin m × Fin n,
        spin (rectangularPrismLayer sigma 0) p) +
      ∑ p : Fin m × Fin n,
        spin (rectangularPrismLayer sigma (Fin.last (2 * h))) p := by
  unfold rectangularPrismPlusBoundaryInteraction
  rw [sum_rectangularPrismSite_eq]
  simp_rw [rectangularPrismBoundaryDegree_split]
  simp_rw [Nat.cast_add, add_mul, Finset.sum_add_distrib]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_comm_three (fun (x : Fin m) (y : Fin n)
    (z : Fin (2 * h + 1)) =>
      (rectangularLayerBoundaryDegree (x, y) : Real) * spin sigma ⟨x, y, z⟩)]
  simp_rw [Fintype.sum_prod_type]
  have hzero (z : Fin (2 * h + 1)) : z.val = 0 ↔ z = 0 := by
    constructor
    · intro hz
      apply Fin.ext
      exact hz
    · intro hz
      subst z
      rfl
  have hlast (z : Fin (2 * h + 1)) :
      z.val + 1 = 2 * h + 1 ↔ z = Fin.last (2 * h) := by
    constructor
    · intro hz
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    · intro hz
      subst z
      simp
  simp_rw [hzero, hlast]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rfl


theorem rectangularPrismPlusExponent_eq_layers
    (J beta : Real) {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) :
    -beta * rectangularPrismPlusEnergy J sigma =
      rectangularLayerFaceBoundary J beta
          (rectangularPrismLayer sigma 0) +
        rectangularLayerFaceBoundary J beta
          (rectangularPrismLayer sigma (Fin.last (2 * h))) +
        (∑ z : Fin (2 * h + 1),
          rectangularLayerBoltzmannInteraction J beta
            (rectangularPrismLayer sigma z)) +
        ∑ z : Fin (2 * h),
          rectangularLayerVerticalInteraction J beta
            (rectangularPrismLayer sigma z.castSucc)
            (rectangularPrismLayer sigma z.succ) := by
  rw [rectangularPrismPlusEnergy,
    rectangularPrismInternalInteraction_eq_layers,
    rectangularPrismPlusBoundaryInteraction_eq_layers]
  unfold rectangularLayerFaceBoundary rectangularLayerBoltzmannInteraction
    rectangularLayerVerticalInteraction
  simp only [← mul_assoc]
  ring_nf
  simp_rw [mul_mul_fintype_sum]
  simp_rw [Finset.sum_add_distrib]
  ring


end
end StatMech.Ising
