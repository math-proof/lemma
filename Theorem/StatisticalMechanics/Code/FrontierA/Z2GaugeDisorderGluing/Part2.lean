/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part3
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.flexible false
set_option linter.style.multiGoal false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem sum_abs_sub_eraseMultibondCouplings
    (J : P → Real) (S : Finset P) :
    (∑ p : P, |J p - eraseMultibondCouplings J S p|) =
      ∑ p ∈ S, |J p| := by
  classical
  calc
    (∑ p : P, |J p - eraseMultibondCouplings J S p|) =
        ∑ p : P, if p ∈ S then |J p| else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p ∈ S <;> simp [eraseMultibondCouplings, hp]
    _ = ∑ p ∈ S, |J p| := by
      rw [← Finset.sum_filter]
      simp only [subset_univ, filter_mem_eq_of_subset]


theorem multibondDisorderFreeEnergy_eraseSeam_sub_abs_le
    (ends : P → V × V) (J : P → Real) (D S : Finset P) :
    |multibondDisorderFreeEnergy ends J D -
        multibondDisorderFreeEnergy ends
          (eraseMultibondCouplings J S) D| ≤
      2 * ∑ p ∈ S, |J p| := by
  simpa only [sum_abs_sub_eraseMultibondCouplings] using
    multibondDisorderFreeEnergy_coupling_sub_abs_le ends J
      (eraseMultibondCouplings J S) D


theorem multibondDisorderFreeEnergy_le_blockCost_add_seam
    (ends : P → V × V) (J : P → Real) (D S : Finset P)
    (blockCost : Real)
    (hblock : multibondDisorderFreeEnergy ends
      (eraseMultibondCouplings J S) D ≤ blockCost) :
    multibondDisorderFreeEnergy ends J D ≤
      blockCost + 2 * ∑ p ∈ S, |J p| := by
  have hdist := multibondDisorderFreeEnergy_eraseSeam_sub_abs_le ends J D S
  have hone := le_trans (le_abs_self
    (multibondDisorderFreeEnergy ends J D -
      multibondDisorderFreeEnergy ends (eraseMultibondCouplings J S) D)) hdist
  linarith


theorem multibondDisorderFreeEnergy_eraseSeam_homogeneous_sub_abs_le
    (ends : P → V × V) (J : Real) (D S : Finset P) :
    |multibondDisorderFreeEnergy ends (fun _ => J) D -
        multibondDisorderFreeEnergy ends
          (eraseMultibondCouplings (fun _ => J) S) D| ≤
      2 * S.card * |J| := by
  simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc] using
    multibondDisorderFreeEnergy_eraseSeam_sub_abs_le ends
      (fun _ => J) D S


theorem cubicalDisorderFreeEnergy_eraseSeam_sub_abs_le
    {a b c : Nat} {beta : Real} (hbeta : 0 < beta)
    (D S : Finset (CubicalPlaquette a b c)) :
    |multibondDisorderFreeEnergy cubicalDualEnds
          (fun _ => gaugeDualCoupling beta) D -
        multibondDisorderFreeEnergy cubicalDualEnds
          (eraseMultibondCouplings (fun _ => gaugeDualCoupling beta) S) D| ≤
      2 * S.card * gaugeDualCoupling beta := by
  have hdual := gaugeDualCoupling_pos hbeta
  simpa [abs_of_pos hdual] using
    multibondDisorderFreeEnergy_eraseSeam_homogeneous_sub_abs_le
      cubicalDualEnds (gaugeDualCoupling beta) D S

end
end StatMech.FrontierA
