/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part5
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

variable (P : PlanarZ2Subgraph) (M : Type*) [Fintype M] [DecidableEq M]


namespace FKIsingDobrushinDomain

variable {P M} (D : FKIsingDobrushinDomain P M)


theorem explorationMass_nonneg (e : M) : 0 ≤ D.explorationMass e := by
  unfold explorationMass
  apply Finset.sum_nonneg
  intro omega homega
  split_ifs
  · exact D.criticalMass_nonneg omega
  · exact le_rfl

theorem explorationMass_le_one (e : M) : D.explorationMass e ≤ 1 := by
  calc
    D.explorationMass e ≤
        ∑ omega : ConfigSpace (Sym2 P.V), D.criticalMass omega := by
      unfold explorationMass
      apply Finset.sum_le_sum
      intro omega homega
      split_ifs
      · exact le_rfl
      · exact D.criticalMass_nonneg omega
    _ = 1 := D.criticalMass_sum_eq_one


theorem fermionicObservable_eq_explorationMass_mul_phase
    (e : M) (phase : Complex)
    (hphase : ∀ omega, e ∈ D.exploration omega →
      D.windingPhase omega e = phase) :
    D.fermionicObservable e = (D.explorationMass e : Complex) * phase := by
  unfold fermionicObservable explorationMass
  calc
    (∑ omega : ConfigSpace (Sym2 P.V), D.fermionicSummand omega e) =
        ∑ omega : ConfigSpace (Sym2 P.V),
          (((if e ∈ D.exploration omega then D.criticalMass omega else 0) :
            Real) : Complex) * phase := by
      apply Finset.sum_congr rfl
      intro omega homega
      by_cases he : e ∈ D.exploration omega
      · simp [fermionicSummand, he, hphase omega he]
      · simp [fermionicSummand, he]
    _ = ((∑ omega : ConfigSpace (Sym2 P.V),
          if e ∈ D.exploration omega then D.criticalMass omega else 0 :
            Real) : Complex) * phase := by
      rw [Complex.ofReal_sum, Finset.sum_mul]


theorem exists_nonnegative_boundary_square_of_phase
    (e : M) (normal phase : Complex) (r : Real)
    (hphase : ∀ omega, e ∈ D.exploration omega →
      D.windingPhase omega e = phase)
    (hr : 0 ≤ r) (hline : normal * phase ^ 2 = (r : Complex)) :
    ∃ t : Real, 0 ≤ t ∧
      normal * D.fermionicObservable e ^ 2 = (t : Complex) := by
  let mass := D.explorationMass e
  refine ⟨mass ^ 2 * r, mul_nonneg (sq_nonneg mass) hr, ?_⟩
  rw [D.fermionicObservable_eq_explorationMass_mul_phase e phase hphase]
  calc
    normal * ((mass : Complex) * phase) ^ 2 =
        (mass : Complex) ^ 2 * (normal * phase ^ 2) := by ring
    _ = (mass : Complex) ^ 2 * (r : Complex) := by rw [hline]
    _ = ((mass ^ 2 * r : Real) : Complex) := by push_cast; ring

theorem fermionicSummand_norm_le (omega : ConfigSpace (Sym2 P.V)) (e : M) :
    ‖D.fermionicSummand omega e‖ <= D.criticalMass omega := by
  unfold fermionicSummand
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (D.criticalMass_nonneg omega), D.norm_windingPhase, mul_one]
  · simpa using D.criticalMass_nonneg omega


theorem norm_fermionicObservable_le_one (e : M) :
    ‖D.fermionicObservable e‖ <= 1 := by
  unfold fermionicObservable
  calc
    ‖∑ omega : ConfigSpace (Sym2 P.V), D.fermionicSummand omega e‖ <=
        ∑ omega : ConfigSpace (Sym2 P.V), ‖D.fermionicSummand omega e‖ :=
      norm_sum_le _ _
    _ <= ∑ omega : ConfigSpace (Sym2 P.V), D.criticalMass omega := by
      exact Finset.sum_le_sum fun omega _ => D.fermionicSummand_norm_le omega e
    _ = 1 := D.criticalMass_sum_eq_one


theorem fermionicObservable_terminal :
    D.fermionicObservable D.terminalEdge = 1 := by
  unfold fermionicObservable fermionicSummand windingPhase
  simp_rw [if_pos (D.terminal_mem _), D.winding_terminal]
  simp only [zero_div, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [← Complex.ofReal_sum, D.criticalMass_sum_eq_one]
  norm_num


end FKIsingDobrushinDomain
end
end StatMech.Universality
