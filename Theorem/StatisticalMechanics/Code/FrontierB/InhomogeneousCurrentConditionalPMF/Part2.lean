/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
import Def.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part2
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness


theorem inhomogeneousFiniteParityPMF_apply
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1) (odd : S -> Bool)
    (a : S -> Nat) :
    inhomogeneousFiniteParityPMF S lambda hlambda odd a =
      ENNReal.ofReal (inhomogeneousFiniteParityKernel S lambda odd a) := by
  rw [inhomogeneousFiniteParityPMF, PMF.normalize_apply,
    tsum_ofReal_inhomogeneousFiniteParityKernel S lambda hlambda odd]
  simp

theorem inhomogeneousFiniteParityPMF_eq_zero_of_ne
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1) (odd : S -> Bool)
    (a : S -> Nat) (hodd : odd ≠ currentLocalParity a) :
    inhomogeneousFiniteParityPMF S lambda hlambda odd a = 0 := by
  rw [inhomogeneousFiniteParityPMF_apply]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hodd
  unfold inhomogeneousFiniteParityKernel
  apply ENNReal.ofReal_eq_zero.mpr
  apply le_of_eq
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases heven : Even (a i)
  · have hpar : currentLocalParity a i = false := by
      simp [currentLocalParity, heven, Nat.not_odd_iff_even.mpr heven]
    have hoddTrue : odd i = true := by
      cases h : odd i <;> simp_all
    simp [parityEdgeKernel, hoddTrue, Nat.not_odd_iff_even.mpr heven]
  · have hoddNat : Odd (a i) := Nat.not_even_iff_odd.mp heven
    have hpar : currentLocalParity a i = true := by
      simp [currentLocalParity, hoddNat]
    have hoddFalse : odd i = false := by
      cases h : odd i <;> simp_all
    simp [parityEdgeKernel, hoddFalse, heven]

theorem bind_inhomogeneousFiniteParityPMF_apply
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1)
    (p : PMF (S -> Bool)) (a : S -> Nat) :
    p.bind (inhomogeneousFiniteParityPMF S lambda hlambda) a =
      p (currentLocalParity a) *
        inhomogeneousFiniteParityPMF S lambda hlambda
          (currentLocalParity a) a := by
  rw [PMF.bind_apply, tsum_eq_single (currentLocalParity a)]
  intro odd hodd
  rw [inhomogeneousFiniteParityPMF_eq_zero_of_ne
    S lambda hlambda odd a hodd]
  simp

end StatMech.FrontierB
