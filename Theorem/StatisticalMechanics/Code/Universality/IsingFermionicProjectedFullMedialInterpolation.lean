/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialRegularity.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiscreteInterpolation.Part4
open Filter Metric Set Topology


noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC


theorem isingProj_sub (e x y : Complex) :
    isingProj e x - isingProj e y = isingProj e (x - y) := by
  unfold isingProj
  rw [map_sub]
  ring


theorem isingProj_norm_le (e z : Complex) (he : Complex.normSq e = 1) :
    ‖isingProj e z‖ ≤ ‖z‖ := by
  have hpair := isingProj_normSq_add_neg e z he
  have hnonneg := Complex.normSq_nonneg (isingProj (-e) z)
  have hsq : Complex.normSq (isingProj e z) ≤ Complex.normSq z := by
    linarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem isingProj_dist_le (e x y : Complex) (he : Complex.normSq e = 1) :
    dist (isingProj e x) (isingProj e y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, isingProj_sub]
  exact isingProj_norm_le e (x - y) he


theorem isingProj_dist_le_of_nearby_holder
    (e : Complex) (F : Complex → Complex)
    (sample embedded observable : Complex) (C alpha : NNReal)
    (he : Complex.normSq e = 1) (hholder : HolderWith C alpha F)
    (hsample : isingProj e (F sample) = observable) :
    dist (isingProj e (F embedded)) observable ≤
      C * dist embedded sample ^ (alpha : Real) := by
  rw [← hsample]
  exact (isingProj_dist_le e (F embedded) (F sample) he).trans
    (hholder.dist_le embedded sample)


theorem norm_sub_le_two_mul_of_proj_one_I
    (x y z : Complex)
    (hxy : isingProj 1 x = isingProj 1 y)
    (hyz : isingProj Complex.I y = isingProj Complex.I z) :
    ‖x - y‖ ≤ 2 * ‖x - z‖ := by
  have hxyRe := congrArg Complex.re hxy
  have hyzRe := congrArg Complex.re hyz
  simp [isingProj] at hxyRe hyzRe
  have hre : x.re = y.re := by linarith
  have him : y.im = y.re - z.re + z.im := by linarith
  have hsq : Complex.normSq (x - y) ≤ 4 * Complex.normSq (x - z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    rw [hre, him]
    nlinarith [sq_nonneg (y.re - z.re), sq_nonneg (x.im - z.im),
      sq_nonneg ((y.re - z.re) + (x.im - z.im)),
      sq_nonneg ((y.re - z.re) - (x.im - z.im))]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith

theorem norm_sub_le_two_mul_of_proj_I_negOne
    (x y z : Complex)
    (hxy : isingProj Complex.I x = isingProj Complex.I y)
    (hyz : isingProj (-1) y = isingProj (-1) z) :
    ‖x - y‖ ≤ 2 * ‖x - z‖ := by
  have hxyRe := congrArg Complex.re hxy
  have hyzIm := congrArg Complex.im hyz
  simp [isingProj] at hxyRe hyzIm
  have him : y.im = z.im := by linarith
  have hre : x.re - y.re = x.im - y.im := by linarith
  have hre' : x.re - y.re = x.im - z.im := by linarith
  have hsq : Complex.normSq (x - y) ≤ 4 * Complex.normSq (x - z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    rw [him, hre']
    nlinarith [sq_nonneg (x.re - z.re), sq_nonneg (x.im - z.im),
      sq_nonneg ((x.re - z.re) + (x.im - z.im)),
      sq_nonneg ((x.re - z.re) - (x.im - z.im))]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith

theorem norm_sub_le_two_mul_of_proj_negOne_negI
    (x y z : Complex)
    (hxy : isingProj (-1) x = isingProj (-1) y)
    (hyz : isingProj (-Complex.I) y = isingProj (-Complex.I) z) :
    ‖x - y‖ ≤ 2 * ‖x - z‖ := by
  have hxyIm := congrArg Complex.im hxy
  have hyzRe := congrArg Complex.re hyz
  simp [isingProj] at hxyIm hyzRe
  have him : x.im = y.im := by linarith
  have hre : y.re = z.re + z.im - y.im := by linarith
  have hsq : Complex.normSq (x - y) ≤ 4 * Complex.normSq (x - z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    rw [him, hre]
    nlinarith [sq_nonneg (x.re - z.re), sq_nonneg (x.im - z.im),
      sq_nonneg ((x.re - z.re) + (x.im - z.im)),
      sq_nonneg ((x.re - z.re) - (x.im - z.im))]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith

theorem norm_sub_le_two_mul_of_proj_negI_one
    (x y z : Complex)
    (hxy : isingProj (-Complex.I) x = isingProj (-Complex.I) y)
    (hyz : isingProj 1 y = isingProj 1 z) :
    ‖x - y‖ ≤ 2 * ‖x - z‖ := by
  have hxyRe := congrArg Complex.re hxy
  have hyzRe := congrArg Complex.re hyz
  simp [isingProj] at hxyRe hyzRe
  have hre : y.re = z.re := by linarith
  have him : x.im - y.im = y.re - x.re := by linarith
  have him' : x.im - y.im = z.re - x.re := by linarith
  have hsq : Complex.normSq (x - y) ≤ 4 * Complex.normSq (x - z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    rw [hre, him']
    nlinarith [sq_nonneg (x.re - z.re), sq_nonneg (x.im - z.im),
      sq_nonneg ((x.re - z.re) + (x.im - z.im)),
      sq_nonneg ((x.re - z.re) - (x.im - z.im))]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith


theorem IsingSquareSHolomorphicQuad.projection_cycle
    (north east south west : Complex)
    (h : IsingSquareSHolomorphicQuad south west north east) :
    isingProj 1 north = isingProj 1 east ∧
      isingProj Complex.I east = isingProj Complex.I south ∧
      isingProj (-1) south = isingProj (-1) west ∧
      isingProj (-Complex.I) west = isingProj (-Complex.I) north := by
  rcases h with ⟨h1, h2, h3⟩
  have h1re := congrArg Complex.re h1
  have h1im := congrArg Complex.im h1
  have h2re := congrArg Complex.re h2
  have h2im := congrArg Complex.im h2
  have h3re := congrArg Complex.re h3
  have h3im := congrArg Complex.im h3
  simp at h1re h1im h2re h2im h3re h3im
  unfold isingProj
  constructor
  · apply Complex.ext <;> simp <;> linarith
  constructor
  · apply Complex.ext <;> simp <;> linarith
  constructor
  · apply Complex.ext <;> simp <;> linarith
  · apply Complex.ext <;> simp <;> linarith


theorem projectionCycle_crossParity_norm_sub_le
    (north east south west : Complex) (delta : Real)
    (hNE : isingProj 1 north = isingProj 1 east)
    (hES : isingProj Complex.I east = isingProj Complex.I south)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
    (hNS : ‖north - south‖ ≤ delta)
    (hEW : ‖east - west‖ ≤ delta) :
    ‖north - east‖ ≤ 2 * delta ∧
      ‖east - south‖ ≤ 2 * delta ∧
      ‖south - west‖ ≤ 2 * delta ∧
      ‖west - north‖ ≤ 2 * delta := by
  constructor
  · exact (norm_sub_le_two_mul_of_proj_one_I north east south hNE hES).trans
      (mul_le_mul_of_nonneg_left hNS (by norm_num))
  constructor
  · exact (norm_sub_le_two_mul_of_proj_I_negOne east south west hES hSW).trans
      (mul_le_mul_of_nonneg_left hEW (by norm_num))
  constructor
  · have h := norm_sub_le_two_mul_of_proj_negOne_negI south west north hSW hWN
    rw [norm_sub_rev] at hNS
    exact h.trans (mul_le_mul_of_nonneg_left hNS (by norm_num))
  · have h := norm_sub_le_two_mul_of_proj_negI_one west north east hWN hNE
    rw [norm_sub_rev] at hEW
    exact h.trans (mul_le_mul_of_nonneg_left hEW (by norm_num))


theorem fkIsingSquareBoundaryRadialPatchFullObservable_even_projectionCycle
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    let north := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j - 1, by omega⟩
    let east := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j, by omega⟩
    let south := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j, by omega⟩
    let west := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    isingProj 1 north = isingProj 1 east ∧
      isingProj Complex.I east = isingProj Complex.I south ∧
      isingProj (-1) south = isingProj (-1) west ∧
      isingProj (-Complex.I) west = isingProj (-Complex.I) north := by
  exact IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _
    (fkIsingSquareBoundaryRadialPatchFullObservable_quad
      n m i j hn hm hi0 hi1 hj0 hj1 heven)


theorem fkIsingSquareBoundaryRadialPatchFullObservable_odd_projectionCycle
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    let north := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j - 1, by omega⟩
    let east := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j, by omega⟩
    let south := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j, by omega⟩
    let west := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    isingProj 1 south = isingProj 1 west ∧
      isingProj Complex.I west = isingProj Complex.I north ∧
      isingProj (-1) north = isingProj (-1) east ∧
      isingProj (-Complex.I) east = isingProj (-Complex.I) south := by
  exact IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _
    (fkIsingSquareBoundaryRadialPatchFullObservable_quad_of_odd
      n m i j hn hm hi0 hi1 hj0 hj1 hodd)

end StatMech.Universality
end
