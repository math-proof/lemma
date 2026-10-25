/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelation
import Lemma.Real.EqSigma.of.EqBilinForm_E_0
import Def.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.DihedralHelpers
open Finset BigOperators Real


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- One-step recurrence for the pair $(A_n, B_n)$ giving the matrix product
that corresponds to applying one more copy of $\sigma_s \sigma_t$. -/
theorem seqAB_step (c : ℝ) : ∀ n,
    seqA c (4 * c ^ 2 - 2) (n + 1) = (4 * c ^ 2 - 1) * seqA c (4 * c ^ 2 - 2) n +
      2 * c * seqB c (4 * c ^ 2 - 2) n ∧
    seqB c (4 * c ^ 2 - 2) (n + 1) = -2 * c * seqA c (4 * c ^ 2 - 2) n -
      seqB c (4 * c ^ 2 - 2) n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  match n with
  | 0 => exact ⟨by simp [seqA, seqB], by simp [seqA, seqB]⟩
  | 1 => exact ⟨by simp [seqA, seqB]; ring, by simp [seqA, seqB]; ring⟩
  | n + 2 =>
    obtain ⟨ihA1, ihB1⟩ := ih (n + 1) (by omega)
    obtain ⟨ihA0, ihB0⟩ := ih n (by omega)
    refine ⟨?_, ?_⟩
    · show seqA c (4 * c ^ 2 - 2) (n + 3) = _
      simp only [seqA, seqB] at ihA1 ihB0 ⊢
      rw [ihB0] at ihA1 ⊢
      nlinarith [mul_self_nonneg c,
                 mul_self_nonneg (seqA c (4 * c ^ 2 - 2) (n + 1)),
                 mul_self_nonneg (seqA c (4 * c ^ 2 - 2) n)]
    · show seqB c (4 * c ^ 2 - 2) (n + 3) = _
      simp only [seqA, seqB] at ihA1 ihB1 ihA0 ihB0 ⊢
      rw [ihB0] at ihA1 ⊢
      rw [ihA0] at ihB1 ⊢
      nlinarith [mul_self_nonneg c,
                 mul_self_nonneg (seqB c (4 * c ^ 2 - 2) (n + 1)),
                 mul_self_nonneg (seqB c (4 * c ^ 2 - 2) n)]


/-- One-step recurrence for the pair $(C_n, D_n)$, analogous to
$\mathtt{seqAB\_step}$. -/
theorem seqCD_step (c : ℝ) : ∀ n,
    seqC c (4 * c ^ 2 - 2) (n + 1) = (4 * c ^ 2 - 1) * seqC c (4 * c ^ 2 - 2) n +
      2 * c * seqD c (4 * c ^ 2 - 2) n ∧
    seqD c (4 * c ^ 2 - 2) (n + 1) = -2 * c * seqC c (4 * c ^ 2 - 2) n -
      seqD c (4 * c ^ 2 - 2) n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  match n with
  | 0 => exact ⟨by simp [seqC, seqD], by simp [seqC, seqD]⟩
  | 1 => exact ⟨by simp [seqC, seqD]; ring, by simp [seqC, seqD]; ring⟩
  | n + 2 =>
    obtain ⟨ihC1, ihD1⟩ := ih (n + 1) (by omega)
    obtain ⟨ihC0, ihD0⟩ := ih n (by omega)
    refine ⟨?_, ?_⟩
    · show seqC c (4 * c ^ 2 - 2) (n + 3) = _
      simp only [seqC, seqD] at ihC1 ihD0 ⊢
      rw [ihD0] at ihC1 ⊢
      nlinarith [mul_self_nonneg c,
                 mul_self_nonneg (seqC c (4 * c ^ 2 - 2) (n + 1)),
                 mul_self_nonneg (seqC c (4 * c ^ 2 - 2) n)]
    · show seqD c (4 * c ^ 2 - 2) (n + 3) = _
      simp only [seqC, seqD] at ihC1 ihD1 ihC0 ihD0 ⊢
      rw [ihD0] at ihC1 ⊢
      rw [ihC0] at ihD1 ⊢
      nlinarith [mul_self_nonneg c,
                 mul_self_nonneg (seqD c (4 * c ^ 2 - 2) (n + 1)),
                 mul_self_nonneg (seqD c (4 * c ^ 2 - 2) n)]


/-- Functional form: the $n$-th iterate of $\sigma_s \sigma_t$ applied to
$e_s$ is the linear combination $A_n\, e_s + B_n\, e_t$. -/
theorem iter_e_s_formula_fn (M : CoxeterMatrix B) (s t : B) (n : ℕ) :
    (fun w => sigma M s (sigma M t w))^[n] (e s) =
      seqA (formVal M s t) (4 * formVal M s t ^ 2 - 2) n • e s +
      seqB (formVal M s t) (4 * formVal M s t ^ 2 - 2) n • e t := by
  induction n with
  | zero => ext u; simp [seqA, seqB]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp]
    rw [ih, sigma_add M t, sigma_smul M t, sigma_smul M t,
        sigma_add M s, sigma_smul M s, sigma_smul M s,
        sigma_comp_e_s, sigma_comp_e_t]
    ext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    set c := formVal M s t
    obtain ⟨hA, hB⟩ := seqAB_step c n
    rw [hA, hB]; ring

/-- Pointwise form of $\mathtt{iter\_e\_s\_formula\_fn}$: evaluating at any
index $u$ gives $A_n\, e_s(u) + B_n\, e_t(u)$. -/
theorem iter_e_s_formula (M : CoxeterMatrix B) (s t : B) (n : ℕ) (u : B) :
    let c := formVal M s t
    let α := 4 * c ^ 2 - 2
    (fun w => sigma M s (sigma M t w))^[n] (e s) u =
      seqA c α n * e s u + seqB c α n * e t u := by
  have h := congr_fun (iter_e_s_formula_fn M s t n) u
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h

/-- Functional form: the $n$-th iterate of $\sigma_s \sigma_t$ applied to
$e_t$ is the linear combination $C_n\, e_s + D_n\, e_t$. -/
theorem iter_e_t_formula_fn (M : CoxeterMatrix B) (s t : B) (n : ℕ) :
    (fun w => sigma M s (sigma M t w))^[n] (e t) =
      seqC (formVal M s t) (4 * formVal M s t ^ 2 - 2) n • e s +
      seqD (formVal M s t) (4 * formVal M s t ^ 2 - 2) n • e t := by
  induction n with
  | zero => ext u; simp [seqC, seqD]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp]
    rw [ih, sigma_add M t, sigma_smul M t, sigma_smul M t,
        sigma_add M s, sigma_smul M s, sigma_smul M s,
        sigma_comp_e_s, sigma_comp_e_t]
    ext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    set c := formVal M s t
    obtain ⟨hC, hD⟩ := seqCD_step c n
    rw [hC, hD]; ring

/-- Pointwise form of $\mathtt{iter\_e\_t\_formula\_fn}$: evaluating at any
index $u$ gives $C_n\, e_s(u) + D_n\, e_t(u)$. -/
theorem iter_e_t_formula (M : CoxeterMatrix B) (s t : B) (n : ℕ) (u : B) :
    let c := formVal M s t
    let α := 4 * c ^ 2 - 2
    (fun w => sigma M s (sigma M t w))^[n] (e t) u =
      seqC c α n * e s u + seqD c α n * e t u := by
  have h := congr_fun (iter_e_t_formula_fn M s t n) u
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h

end CoxeterGroup
