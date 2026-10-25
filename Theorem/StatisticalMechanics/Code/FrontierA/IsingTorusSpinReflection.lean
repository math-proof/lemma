/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.QuadraticDiscriminant
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorusHalfReflectionForm_add_left
    (i : Fin d) (beta : Real)
    (F G H : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
    isingTorusHalfReflectionForm i beta (F + G) H =
      isingTorusHalfReflectionForm i beta F H +
        isingTorusHalfReflectionForm i beta G H := by
  unfold isingTorusHalfReflectionForm
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro lower _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro upper _
  ring

theorem isingTorusHalfReflectionForm_smul_left
    (i : Fin d) (beta t : Real)
    (F G : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
    isingTorusHalfReflectionForm i beta (t • F) G =
      t * isingTorusHalfReflectionForm i beta F G := by
  unfold isingTorusHalfReflectionForm
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lower _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro upper _
  ring

theorem isingTorusHalfReflectionForm_symm
    (i : Fin d) (beta : Real)
    (F G : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
    isingTorusHalfReflectionForm i beta F G =
      isingTorusHalfReflectionForm i beta G F := by
  unfold isingTorusHalfReflectionForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro lower _
  apply Finset.sum_congr rfl
  intro upper _
  have hdot :
      (∑ e : IsingTorusDirectedEdge d k,
          isingTorusBoundaryFeature i
              (isingTorusLowerValues i 0 upper) e *
            isingTorusBoundaryFeature i
              (isingTorusLowerValues i 0 lower) e) =
        ∑ e : IsingTorusDirectedEdge d k,
          isingTorusBoundaryFeature i
              (isingTorusLowerValues i 0 lower) e *
            isingTorusBoundaryFeature i
              (isingTorusLowerValues i 0 upper) e := by
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hdot]
  ring

theorem isingTorusHalfReflectionForm_add_right
    (i : Fin d) (beta : Real)
    (F G H : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
    isingTorusHalfReflectionForm i beta F (G + H) =
      isingTorusHalfReflectionForm i beta F G +
        isingTorusHalfReflectionForm i beta F H := by
  rw [isingTorusHalfReflectionForm_symm,
    isingTorusHalfReflectionForm_add_left,
    isingTorusHalfReflectionForm_symm i beta G F,
    isingTorusHalfReflectionForm_symm i beta H F]

theorem isingTorusHalfReflectionForm_smul_right
    (i : Fin d) (beta t : Real)
    (F G : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
    isingTorusHalfReflectionForm i beta F (t • G) =
      t * isingTorusHalfReflectionForm i beta F G := by
  rw [isingTorusHalfReflectionForm_symm,
    isingTorusHalfReflectionForm_smul_left,
    isingTorusHalfReflectionForm_symm i beta G F]


theorem isingTorusHalfReflectionForm_nonneg
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (F : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
    0 ≤ isingTorusHalfReflectionForm i beta F F := by
  exact exp_dotProduct_kernel_quadratic_nonneg beta hbeta
    (fun sigma e => isingTorusBoundaryFeature i
      (isingTorusLowerValues i 0 sigma) e)
    (fun sigma => isingTorusLowerHalfWeight i beta
      (isingTorusLowerValues i 0 sigma) * F sigma)

theorem quadratic_nonneg_cauchy
    (aa ab bb : Real)
    (h : ∀ t : Real, 0 ≤ aa + 2 * t * ab + t ^ 2 * bb) :
    ab ^ 2 ≤ aa * bb := by
  have hd : discrim bb (2 * ab) aa ≤ 0 :=
    discrim_le_zero (a := bb) (b := 2 * ab) (c := aa) (by
      intro t
      have ht := h t
      nlinarith)
  unfold discrim at hd
  nlinarith


theorem isingTorusHalfReflectionForm_cauchy
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (F G : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
    isingTorusHalfReflectionForm i beta F G ^ 2 ≤
      isingTorusHalfReflectionForm i beta F F *
        isingTorusHalfReflectionForm i beta G G := by
  apply quadratic_nonneg_cauchy
  intro t
  have h := isingTorusHalfReflectionForm_nonneg i beta hbeta
    (F + t • G)
  rw [isingTorusHalfReflectionForm_add_left,
    isingTorusHalfReflectionForm_add_right,
    isingTorusHalfReflectionForm_add_right,
    isingTorusHalfReflectionForm_smul_left,
    isingTorusHalfReflectionForm_smul_right,
    isingTorusHalfReflectionForm_smul_left,
    isingTorusHalfReflectionForm_smul_right,
    isingTorusHalfReflectionForm_symm i beta G F] at h
  nlinarith


end StatMech.FrontierA
