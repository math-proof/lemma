/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part8
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorusSiteReflectionForm_eq_amplitudes
    (i : Fin d) (beta : Real)
    (F G : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) :
    isingTorusSiteReflectionForm i beta F G =
      ∑ boundary : ConfigSpace (IsingTorusSitePlane (k := k) i),
        isingTorusSiteBoundaryAmplitude i beta boundary F *
          isingTorusSiteBoundaryAmplitude i beta boundary G := by
  unfold isingTorusSiteReflectionForm isingTorusSiteBoundaryAmplitude
  apply Finset.sum_congr rfl
  intro boundary _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro lower _
  rw [Finset.mul_sum]

theorem isingTorusSiteReflectionForm_nonneg
    (i : Fin d) (beta : Real)
    (F : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) :
    0 ≤ isingTorusSiteReflectionForm i beta F F := by
  rw [isingTorusSiteReflectionForm_eq_amplitudes]
  exact Finset.sum_nonneg fun boundary _ =>
    mul_self_nonneg (isingTorusSiteBoundaryAmplitude i beta boundary F)

theorem isingTorusSiteReflectionForm_cauchy
    (i : Fin d) (beta : Real)
    (F G : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) :
    isingTorusSiteReflectionForm i beta F G ^ 2 ≤
      isingTorusSiteReflectionForm i beta F F *
        isingTorusSiteReflectionForm i beta G G := by
  simp_rw [isingTorusSiteReflectionForm_eq_amplitudes]
  simpa only [pow_two] using sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun boundary : ConfigSpace (IsingTorusSitePlane (k := k) i) =>
      isingTorusSiteBoundaryAmplitude i beta boundary F)
    (fun boundary : ConfigSpace (IsingTorusSitePlane (k := k) i) =>
      isingTorusSiteBoundaryAmplitude i beta boundary G)

end StatMech.FrontierA
