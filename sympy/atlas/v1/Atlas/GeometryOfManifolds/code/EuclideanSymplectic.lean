/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanSymplectic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.EuclideanDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.EuclideanDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds

noncomputable section

open EuclideanΩ

/-- Every element of `Fin 2` is either `0` or `1`. -/
lemma Fin2_eq_zero_or_one (k : Fin 2) : k = 0 ∨ k = 1 := by
  rcases k with ⟨k, hk⟩; simp only [Fin.ext_iff]; omega

/-- Standard symplectic alternating $2$-form on $\mathbb{R}^{2n}$:
$\Omega(u, v) = \sum_{i=1}^{n} (u_i v_{n+i} - u_{n+i} v_i)$, with the $(e_i, f_i)$ basis given by
$f_i = e_{n+i}$ so that $\Omega(e_i, f_j) = \delta_{ij}$. -/
def standardSymplecticAlt (n : ℕ) : Eℝ (2 * n) [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  AlternatingMap.mk
    { toFun := fun v =>
        ∑ i : Fin n, (v 0 ⟨i.val, by omega⟩ * v 1 ⟨n + i.val, by omega⟩ -
                      v 0 ⟨n + i.val, by omega⟩ * v 1 ⟨i.val, by omega⟩)
      map_update_add' := fun v k u₁ u₂ => by
        classical
        have h01 : (0 : Fin 2) ≠ 1 := by omega
        have h10 : (1 : Fin 2) ≠ 0 := by omega
        rcases Fin2_eq_zero_or_one k with rfl | rfl
        · simp_rw [Function.update_self, Function.update_of_ne h10]
          rw [← Finset.sum_add_distrib]; congr 1; ext i
          simp only [PiLp.add_apply]; ring
        · simp_rw [Function.update_self, Function.update_of_ne h01]
          rw [← Finset.sum_add_distrib]; congr 1; ext i
          simp only [PiLp.add_apply]; ring
      map_update_smul' := fun v k r u => by
        classical
        have h01 : (0 : Fin 2) ≠ 1 := by omega
        have h10 : (1 : Fin 2) ≠ 0 := by omega
        rcases Fin2_eq_zero_or_one k with rfl | rfl
        · simp only [smul_eq_mul]
          simp_rw [Function.update_self, Function.update_of_ne h10]
          rw [Finset.mul_sum]; congr 1; ext i
          simp only [PiLp.smul_apply, smul_eq_mul]; ring
        · simp only [smul_eq_mul]
          simp_rw [Function.update_self, Function.update_of_ne h01]
          rw [Finset.mul_sum]; congr 1; ext i
          simp only [PiLp.smul_apply, smul_eq_mul]; ring }
    (fun v i j hij hveq => by
      have h01 : v 0 = v 1 := by
        rcases Fin2_eq_zero_or_one i with rfl | rfl <;>
          rcases Fin2_eq_zero_or_one j with rfl | rfl <;> simp_all
      simp_rw [h01]
      apply Finset.sum_eq_zero; intro k _; ring)

/-- The standard symplectic $2$-form on $\mathbb{R}^{2n}$ viewed as a constant differential form. -/
def standardSymplecticForm (n : ℕ) : EuclideanΩ (2 * n) 2 :=
  fun _ => standardSymplecticAlt n
