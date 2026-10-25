/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Def.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part4
set_option autoImplicit false

open DifferentialFormSpace


/-- Positivity of the Weitzenböck constant: $c_G > 0$. -/
theorem weitzenbock_uniform_constant_pos
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [wb : HasWeitzenbockDecomp Ω l2 dol] :
    weitzenbock_uniform_constant_axiom l2 dol > 0 :=
  wb.c_G_pos

/-- Uniform $L^2$ bound from the Weitzenböck decomposition: for all $k \ne 0$,
$\|G(s)\|_{L^2}^2 \le (c_G/k)\, \|\bar\partial s\|_{L^2}^2$. -/
theorem weitzenbock_uniform_l2_bound_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [wb : HasWeitzenbockDecomp Ω l2 dol] :
    ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),

      l2.l2norm ((weitzenbock_green_operator_axiom l2 dol).greenCorrection k s) *
        l2.l2norm ((weitzenbock_green_operator_axiom l2 dol).greenCorrection k s) ≤
        (weitzenbock_uniform_constant_axiom l2 dol) / (k : ℝ) *
          (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s)) :=
  wb.uniform_l2_bound


/-- Elementary inequality: $y \cdot e^{-y} \le e^{-1}$ for all $y \in \mathbb{R}$,
attained at $y = 1$. -/
theorem mul_exp_neg_le_exp_neg_one (y : ℝ) :
    y * Real.exp (-y) ≤ Real.exp (-1) := by
  have hexp_ineq : y ≤ Real.exp (y - 1) := by
    have := Real.add_one_le_exp (y - 1); linarith
  calc y * Real.exp (-y)
      ≤ Real.exp (y - 1) * Real.exp (-y) := by
        apply mul_le_mul_of_nonneg_right hexp_ineq (le_of_lt (Real.exp_pos _))
    _ = Real.exp ((y - 1) + (-y)) := by rw [← Real.exp_add]
    _ = Real.exp (-1) := by ring_nf

/-- Rescaled form of `mul_exp_neg_le_exp_neg_one`:
$t \cdot e^{-\lambda t} \le 1 / (\lambda e)$ for $\lambda > 0$ and all $t \in \mathbb{R}$. -/
theorem t_exp_neg_lam_t_bound (t lam : ℝ) (hlam_pos : lam > 0) :
    t * Real.exp (-lam * t) ≤ 1 / (lam * Real.exp 1) := by
  by_cases ht : 0 ≤ t
  · have h_ue := mul_exp_neg_le_exp_neg_one (lam * t)
    have h_eq : t * Real.exp (-lam * t) =
        (1 / lam) * (lam * t * Real.exp (-(lam * t))) := by field_simp
    rw [h_eq]
    calc (1 / lam) * (lam * t * Real.exp (-(lam * t)))
        ≤ (1 / lam) * Real.exp (-1) := by
          apply mul_le_mul_of_nonneg_left h_ue; positivity
      _ = 1 / (lam * Real.exp 1) := by rw [Real.exp_neg]; field_simp
  · push_neg at ht
    have h1 : t * Real.exp (-lam * t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt ht) (le_of_lt (Real.exp_pos _))
    linarith [show (0 : ℝ) < 1 / (lam * Real.exp 1) from by positivity]

/-- Absorption lemma: $A\,t\,e^{-\lambda_0 t} \le C_g\, e^{-\lambda t}$ for some
$C_g, \lambda > 0$ and all $t \ge 0$. The polynomial factor $t$ is absorbed
into a slightly smaller exponential rate. -/
theorem absorb_poly_into_exp (A lam0 : ℝ) (hA : A > 0) (hlam0 : lam0 > 0) :
    ∃ (C_g lam : ℝ), C_g > 0 ∧ lam > 0 ∧
      ∀ (t : ℝ), 0 ≤ t →
        A * t * Real.exp (-lam0 * t) ≤ C_g * Real.exp (-lam * t) := by
  refine ⟨A / (lam0 / 2 * Real.exp 1) + 1, lam0 / 2, by positivity, by linarith, ?_⟩
  intro t ht
  have hlam_pos : lam0 / 2 > 0 := by linarith
  have hexp_split : Real.exp (-lam0 * t) =
      Real.exp (-(lam0 / 2) * t) * Real.exp (-(lam0 / 2) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  calc A * t * Real.exp (-lam0 * t)
      = A * t * (Real.exp (-(lam0/2) * t) * Real.exp (-(lam0/2) * t)) := by rw [hexp_split]
    _ = (A * (t * Real.exp (-(lam0/2) * t))) * Real.exp (-(lam0/2) * t) := by ring
    _ ≤ (A * (1 / ((lam0/2) * Real.exp 1))) * Real.exp (-(lam0/2) * t) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left
              (t_exp_neg_lam_t_bound t (lam0/2) hlam_pos) (le_of_lt hA)
        · exact le_of_lt (Real.exp_pos _)
    _ = A / ((lam0/2) * Real.exp 1) * Real.exp (-(lam0/2) * t) := by ring
    _ ≤ (A / ((lam0/2) * Real.exp 1) + 1) * Real.exp (-(lam0/2) * t) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
        linarith

