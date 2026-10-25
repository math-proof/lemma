/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part15


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


theorem det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitnessFiber
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        ∑ X : finiteCRSFWitnessFiber next,
          finiteCRSFWitnessTerm conductance transport X := by
  rw [det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitness]
  symm
  exact Fintype.sum_fiberwise finiteCRSFWitnessNext
    (finiteCRSFWitnessTerm conductance transport)


theorem det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupport
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        ∑ S : finiteCRSFCycleSupport next,
          finiteCRSFWitnessTerm conductance transport S.toFiber := by
  rw [det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitnessFiber]
  apply Finset.sum_congr rfl
  intro next _
  exact Fintype.sum_equiv
    (finiteCRSFWitnessFiberEquivCRSFCycleSupport next)
    (fun X : finiteCRSFWitnessFiber next =>
      finiteCRSFWitnessTerm conductance transport X)
    (fun S : finiteCRSFCycleSupport next =>
      finiteCRSFWitnessTerm conductance transport S.toFiber)
    (fun X => by
      change finiteCRSFWitnessTerm conductance transport X.1 =
        finiteCRSFWitnessTerm conductance transport
          X.toCycleSupport.toFiber.1
      exact congrArg (finiteCRSFWitnessTerm conductance transport)
        (congrArg Subtype.val X.toFiber_toCycleSupport.symm))


theorem det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupportTerm
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        ∑ S : finiteCRSFCycleSupport next,
          S.term conductance transport := by
  rw [det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupport]
  apply Finset.sum_congr rfl
  intro next _
  apply Finset.sum_congr rfl
  intro S _
  exact finiteCRSFWitnessTerm_toFiber conductance transport next S


theorem det_finiteTwistedLaplacian_eq_sum_atomicCycleHolonomies
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        (∏ v : V, conductance v (next v)) *
          ∑ S : finiteCRSFCycleSupport next,
            (-1 : Complex) ^ S.atomicCycles.card *
              ∏ cycle ∈ S.atomicCycles,
                S.atomicCycleHolonomy transport cycle := by
  rw [det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupportTerm]
  apply Finset.sum_congr rfl
  intro next _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [S.term_eq_atomicCycleHolonomies]
  ring


theorem finiteTwistedLaplacian_trivial_mulVec_one
    (conductance : V -> V -> Complex)
    (hdiag : forall v, conductance v v = 0) :
    finiteTwistedLaplacian conductance (fun _ _ => 1) *ᵥ
        (fun _ => (1 : Complex)) = 0 := by
  funext v
  rw [Matrix.mulVec, dotProduct]
  simp only [mul_one, Pi.zero_apply]
  rw [← Finset.sum_erase_add Finset.univ
    (fun w => finiteTwistedLaplacian conductance (fun _ _ => 1) v w)
    (Finset.mem_univ v)]
  simp only [finiteTwistedLaplacian, if_pos]
  have hoff :
      (∑ x ∈ Finset.univ.erase v,
        if v = x then ∑ u, conductance v u else -conductance v x * 1) =
        ∑ x ∈ Finset.univ.erase v, -conductance v x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxne : x ≠ v := Finset.ne_of_mem_erase hx
    simp [hxne.symm]
  rw [hoff, ← Finset.sum_erase_add Finset.univ
    (fun w => conductance v w) (Finset.mem_univ v)]
  rw [hdiag]
  simp


theorem det_finiteTwistedLaplacian_trivial_eq_zero
    [Nonempty V] (conductance : V -> V -> Complex)
    (hdiag : forall v, conductance v v = 0) :
    (finiteTwistedLaplacian conductance (fun _ _ => 1)).det = 0 := by
  let v0 : V := Classical.choice (inferInstance : Nonempty V)
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (finiteTwistedLaplacian_trivial_mulVec_one conductance hdiag)
    (i := v0)
  simp


theorem finiteTwistedLaplacian_const_mul
    (a : Complex) (conductance transport : V -> V -> Complex) :
    finiteTwistedLaplacian (fun v w => a * conductance v w) transport =
      a • finiteTwistedLaplacian conductance transport := by
  ext v w
  by_cases hvw : v = w
  · subst w
    simp [finiteTwistedLaplacian, Finset.mul_sum]
  · simp [finiteTwistedLaplacian, hvw]
    ring


theorem det_finiteTwistedLaplacian_const_mul
    (a : Complex) (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian (fun v w => a * conductance v w)
        transport).det =
      a ^ Fintype.card V *
        (finiteTwistedLaplacian conductance transport).det := by
  rw [finiteTwistedLaplacian_const_mul, Matrix.det_smul]


end StatMech.FrontierA
