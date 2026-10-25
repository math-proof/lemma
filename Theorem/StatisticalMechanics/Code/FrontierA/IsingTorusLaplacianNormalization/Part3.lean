/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusExponentialMoment
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusLaplacianNormalization.Part2
open Finset Matrix
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorusDirichlet_eq_lapMatrix_quadratic
    (h : IsingDyadicTorus d k → Real) :
    isingTorusDirichlet h =
      h ⬝ᵥ ((isingTorusGraph d k).lapMatrix Real *ᵥ h) := by
  rw [← Matrix.toLinearMap₂'_apply']
  rw [SimpleGraph.lapMatrix_toLinearMap₂']
  let F : IsingDyadicTorus d k × IsingDyadicTorus d k → Real :=
    fun p => (h p.1 - h p.2) ^ 2
  have hadjSum :
      (∑ x : IsingDyadicTorus d k,
          ∑ y : IsingDyadicTorus d k,
            if (isingTorusGraph d k).Adj x y
            then (h x - h y) ^ 2 else 0) =
        ∑ dart : (isingTorusGraph d k).Dart,
          (h dart.fst - h dart.snd) ^ 2 := by
    calc
      (∑ x : IsingDyadicTorus d k,
          ∑ y : IsingDyadicTorus d k,
            if (isingTorusGraph d k).Adj x y
            then (h x - h y) ^ 2 else 0) =
          ∑ p : IsingDyadicTorus d k × IsingDyadicTorus d k,
            if (isingTorusGraph d k).Adj p.1 p.2 then F p else 0 := by
        exact (Fintype.sum_prod_type (fun p :
          IsingDyadicTorus d k × IsingDyadicTorus d k =>
            if (isingTorusGraph d k).Adj p.1 p.2 then F p else 0)).symm
      _ = (∑ p ∈ Finset.univ.filter
            (fun p => (isingTorusGraph d k).Adj p.1 p.2), F p) := by
        rw [Finset.sum_filter]
      _ = ∑ p : {p : IsingDyadicTorus d k × IsingDyadicTorus d k //
            (isingTorusGraph d k).Adj p.1 p.2}, F p := by
        exact Finset.sum_subtype
          (p := fun p : IsingDyadicTorus d k × IsingDyadicTorus d k =>
            (isingTorusGraph d k).Adj p.1 p.2)
          (s := Finset.univ.filter fun p =>
            (isingTorusGraph d k).Adj p.1 p.2) (by simp) F
      _ = ∑ dart : (isingTorusGraph d k).Dart,
            (h dart.fst - h dart.snd) ^ 2 := by
        rw [← (torusDartProdEquiv (d := d) (k := k)).sum_comp]
        rfl
  have hdartSum :
      (∑ dart : (isingTorusGraph d k).Dart,
          (h dart.fst - h dart.snd) ^ 2) =
        2 * isingTorusDirichlet h := by
    rw [← (isingTorusOrientedIndexedDartEquiv
      (d := d) (k := k)).sum_comp]
    unfold isingTorusDirichlet isingTorusDirichletBilinear
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [isingTorusOrientedIndexedDartEquiv,
      isingTorusOrientedIndexedDart, isingTorusIndexedDart]
    ring
  rw [hadjSum, hdartSum]
  ring


theorem isingTorusDirichletBilinear_eq_lapMatrix
    (u h : IsingDyadicTorus d k → Real) :
    isingTorusDirichletBilinear u h =
      u ⬝ᵥ ((isingTorusGraph d k).lapMatrix Real *ᵥ h) := by
  have hadd := isingTorusDirichlet_add u h
  rw [isingTorusDirichlet_eq_lapMatrix_quadratic,
    isingTorusDirichlet_eq_lapMatrix_quadratic,
    isingTorusDirichlet_eq_lapMatrix_quadratic] at hadd
  have hsymm := (isingTorusGraph d k).isSymm_lapMatrix Real
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct] at hadd
  have hcross :
      h ⬝ᵥ ((isingTorusGraph d k).lapMatrix Real *ᵥ u) =
        u ⬝ᵥ ((isingTorusGraph d k).lapMatrix Real *ᵥ h) := by
    rw [← Matrix.dotProduct_transpose_mulVec]
    rw [hsymm.eq]
  rw [hcross] at hadd
  linarith

end StatMech.FrontierA
