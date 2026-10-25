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
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusLaplacianNormalization.Part3
open Finset Matrix
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorus_lapMatrix_range_eq_zeroSum :
    LinearMap.range
        (Matrix.toLin' ((isingTorusGraph d k).lapMatrix Real)) =
      LinearMap.ker (isingTorusSumLinear (d := d) (k := k)) := by
  let G := isingTorusGraph d k
  let L := Matrix.toLin' (G.lapMatrix Real)
  let S := isingTorusSumLinear (d := d) (k := k)
  have hle : LinearMap.range L ≤ LinearMap.ker S := by
    rintro _ ⟨h, rfl⟩
    rw [LinearMap.mem_ker]
    change ∑ x, (G.lapMatrix Real *ᵥ h) x = 0
    rw [← one_dotProduct]
    rw [← G.isSymm_lapMatrix Real]
    rw [Matrix.dotProduct_transpose_mulVec]
    have hone := G.lapMatrix_mulVec_const_eq_zero (R := Real)
    change h ⬝ᵥ (G.lapMatrix Real *ᵥ (fun _ => (1 : Real))) = 0
    rw [hone, dotProduct_zero]
  have hconn : G.Connected := isingTorusGraph_connected
  letI : Subsingleton G.ConnectedComponent :=
    hconn.preconnected.subsingleton_connectedComponent
  have hkerL : Module.finrank Real (LinearMap.ker L) = 1 := by
    calc
      Module.finrank Real (LinearMap.ker L) =
          Fintype.card G.ConnectedComponent :=
        (G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix).symm
      _ = 1 := Fintype.card_eq_one_iff.mpr
        ⟨G.connectedComponentMk 0, fun _ => Subsingleton.elim _ _⟩
  have hSsurj : Function.Surjective S := by
    intro r
    refine ⟨Pi.single (0 : IsingDyadicTorus d k) r, ?_⟩
    simp [S, isingTorusSumLinear]
  have hSrange : LinearMap.range S = ⊤ :=
    LinearMap.range_eq_top.mpr hSsurj
  have hSrangeRank : Module.finrank Real (LinearMap.range S) = 1 := by
    rw [hSrange]
    simp
  have hLdim := L.finrank_range_add_finrank_ker
  have hSdim := S.finrank_range_add_finrank_ker
  rw [hkerL] at hLdim
  rw [hSrangeRank] at hSdim
  apply Submodule.eq_of_le_of_finrank_eq hle
  omega


theorem exists_isingTorusDirichlet_potential
    (f : IsingDyadicTorus d k → Real)
    (hzero : ∑ x, f x = 0) :
    ∃ h : IsingDyadicTorus d k → Real,
      ∀ u : IsingDyadicTorus d k → Real,
        isingTorusDirichletBilinear u h = ∑ x, u x * f x := by
  have hfker : f ∈ LinearMap.ker
      (isingTorusSumLinear (d := d) (k := k)) := by
    simpa [LinearMap.mem_ker, isingTorusSumLinear] using hzero
  rw [← isingTorus_lapMatrix_range_eq_zeroSum] at hfker
  obtain ⟨h, hh⟩ := hfker
  refine ⟨h, fun u => ?_⟩
  rw [isingTorusDirichletBilinear_eq_lapMatrix]
  rw [← Matrix.toLin'_apply, hh]
  rfl


theorem isingTorus_linear_expMoment_le_unconditional
    (beta : Real) (hbeta : 0 < beta)
    (f h : IsingDyadicTorus d k → Real)
    (hpotential : ∀ u : IsingDyadicTorus d k → Real,
      isingTorusDirichletBilinear u h = ∑ x, u x * f x)
    (s : Real) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Real.exp (s * ∑ x, isingTorusSpinField sigma x * f x)) /
      isingTorusShiftedPartition (d := d) (k := k) beta 0 ≤
        Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
  have hmgf := isingTorus_bilinear_expMoment_le_unconditional
    (d := d) (k := k) beta hbeta (-s / beta) h
  simp_rw [hpotential] at hmgf
  convert hmgf using 1 <;> field_simp


theorem isingTorus_linear_expAbsMoment_le_unconditional
    (beta : Real) (hbeta : 0 < beta)
    (f h : IsingDyadicTorus d k → Real)
    (hpotential : ∀ u : IsingDyadicTorus d k → Real,
      isingTorusDirichletBilinear u h = ∑ x, u x * f x)
    (s : Real) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Real.exp (s * |∑ x, isingTorusSpinField sigma x * f x|)) /
      isingTorusShiftedPartition (d := d) (k := k) beta 0 ≤
        2 * Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
  have hmgf := isingTorus_bilinear_expAbsMoment_le_unconditional
    (d := d) (k := k) beta hbeta (s / beta) h
  simp_rw [hpotential] at hmgf
  have hbeta0 : beta ≠ 0 := hbeta.ne'
  convert hmgf using 1
  · apply congrArg (fun z : Real => z / isingTorusShiftedPartition
        (d := d) (k := k) beta 0)
    apply Finset.sum_congr rfl
    intro sigma _
    congr 2
    rw [abs_mul, abs_of_pos hbeta]
    field_simp
  · field_simp


theorem exists_isingTorus_linear_expMoment_bounds
    (beta : Real) (hbeta : 0 < beta)
    (f : IsingDyadicTorus d k → Real)
    (hzero : ∑ x, f x = 0) :
    ∃ h : IsingDyadicTorus d k → Real,
      (∀ u : IsingDyadicTorus d k → Real,
        isingTorusDirichletBilinear u h = ∑ x, u x * f x) ∧
      (∀ s : Real,
        (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
            Real.exp (-(beta / 2) *
              isingTorusDirichlet (isingTorusSpinField sigma)) *
            Real.exp (s * ∑ x,
              isingTorusSpinField sigma x * f x)) /
          isingTorusShiftedPartition (d := d) (k := k) beta 0 ≤
            Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta))) ∧
      (∀ s : Real,
        (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
            Real.exp (-(beta / 2) *
              isingTorusDirichlet (isingTorusSpinField sigma)) *
            Real.exp (s * |∑ x,
              isingTorusSpinField sigma x * f x|)) /
          isingTorusShiftedPartition (d := d) (k := k) beta 0 ≤
            2 * Real.exp
              (s ^ 2 * isingTorusDirichlet h / (2 * beta))) := by
  obtain ⟨h, hpotential⟩ := exists_isingTorusDirichlet_potential f hzero
  exact ⟨h, hpotential,
    fun s => isingTorus_linear_expMoment_le_unconditional
      beta hbeta f h hpotential s,
    fun s => isingTorus_linear_expAbsMoment_le_unconditional
      beta hbeta f h hpotential s⟩

end StatMech.FrontierA
