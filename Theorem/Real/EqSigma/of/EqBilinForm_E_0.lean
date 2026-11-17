/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelation.lean -/

module

public import Mathlib
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3

public section

open Finset BigOperators CoxeterGroup


/--
[sigma_fixes_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelation.lean)
-/
public theorem sigma_fixes_orthogonal_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {v : B → ℝ}
-- given
  (h : bilinForm M v (e s) = 0) :
-- imply
  sigma M s v = v := by
-- proof
  ext t
  simp only [sigma, h]
  ring

/--
[sigma_comp_fixes_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelation.lean)
-/
public theorem sigma_comp_fixes_orthogonal_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hs : bilinForm M v (e s) = 0)
  (ht : bilinForm M v (e t) = 0) :
-- imply
  sigma M s (sigma M t v) = v := by
-- proof
  rw [sigma_fixes_orthogonal_eq ht, sigma_fixes_orthogonal_eq hs]

/--
[sigma_comp_e_s](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelation.lean)
-/
public theorem sigma_comp_e_s_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B} :
-- imply
  sigma M s (sigma M t (e s)) = fun u => (4 * formVal M s t ^ 2 - 1) * e s u - 2 * formVal M s t * e t u := by
-- proof
  have add_left (v₁ v₂ w : B → ℝ) :
      bilinForm M (v₁ + v₂) w = bilinForm M v₁ w + bilinForm M v₂ w := by
    simp only [bilinForm, Pi.add_apply, add_mul]
    simp_rw [Finset.sum_add_distrib]
  have smul_left (c : ℝ) (v w : B → ℝ) :
      bilinForm M (c • v) w = c * bilinForm M v w := by
    simp only [bilinForm, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro _ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro _ _
    ring
  have hσt : sigma M t (e s) = e s + (-2 * formVal M s t) • e t := by
    ext u
    simp only [sigma, bilinForm_e_e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hB : bilinForm M (sigma M t (e s)) (e s) = 1 - 2 * formVal M s t ^ 2 := by
    rw [hσt, add_left, smul_left, bilinForm_e_e, bilinForm_e_e, formVal_diag,
      formVal_symm M t s]
    ring
  ext u
  simp only [sigma]
  rw [hB, bilinForm_e_e]
  ring

/--
[sigma_comp_e_t](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelation.lean)
-/
public theorem sigma_comp_e_t_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B} :
-- imply
  sigma M s (sigma M t (e t)) = fun u => 2 * formVal M s t * e s u - e t u := by
-- proof
  have smul_left (c : ℝ) (v w : B → ℝ) :
      bilinForm M (c • v) w = c * bilinForm M v w := by
    simp only [bilinForm, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro _ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro _ _
    ring
  have hσt : sigma M t (e t) = (-1 : ℝ) • e t := by
    ext u
    simp only [sigma, bilinForm_e_e, formVal_diag, Pi.smul_apply, smul_eq_mul]
    ring
  have hB : bilinForm M (sigma M t (e t)) (e s) = -formVal M t s := by
    rw [hσt, smul_left, bilinForm_e_e]
    ring
  ext u
  simp only [sigma]
  rw [hB, bilinForm_e_e, formVal_diag, formVal_symm M t s]
  ring


-- created on 2026-10-23
