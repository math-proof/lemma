module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.DihedralHelpers.Part2

public section

open Finset BigOperators Real CoxeterGroup


/--
[sin_chebyshev_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem sin_chebyshev_step
  {θ x : ℝ} :
-- imply
  2 * cos (2 * θ) * sin x - sin (x - 2 * θ) = sin (x + 2 * θ) := by
-- proof
  linarith [Real.sin_add x (2 * θ), Real.sin_sub x (2 * θ)]


/--
[seqC_eq_neg_seqB](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem seqC_eq_neg_seqB
  {c α : ℝ} :
-- imply
  ∀ n, seqC c α n = -seqB c α n := by
-- proof
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [seqC, seqB]
    | 1 => simp [seqC, seqB]
    | n + 2 =>
      simp only [seqC, seqB]
      rw [ih (n + 1) (by omega), ih n (by omega)]; ring


/--
[seqA_sin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem seqA_sin
  {c α θ : ℝ}
-- given
  (hc : c = -cos θ)
  (hα : α = 4 * c ^ 2 - 2) :
-- imply
  ∀ n, sin θ * seqA c α n = sin ((2 * (n : ℝ) + 1) * θ) := by
-- proof
  have hα_cos : α = 2 * cos (2 * θ) := by rw [hα, hc, cos_two_mul]; ring
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 =>
      simp only [seqA, mul_one]
      ring_nf
    | 1 =>
      simp only [seqA, hc, neg_sq]
      rw [show (2 * (↑(1 : ℕ) : ℝ) + 1) * θ = 3 * θ by push_cast; ring, sin_three_mul θ]
      have : cos θ ^ 2 = 1 - sin θ ^ 2 := by linarith [sin_sq_add_cos_sq θ]
      rw [this]; ring
    | n + 2 =>
      calc
        _ = α * (sin θ * seqA c α (n + 1)) - (sin θ * seqA c α n) := by
          simp only [seqA]
          ring
        _ = α * sin ((2 * ↑(n + 1) + 1) * θ) - sin ((2 * ↑n + 1) * θ) := by
          rw [ih (n + 1) (by omega), ih n (by omega)]
        _ = 2 * cos (2 * θ) * sin ((2 * ↑(n + 1) + 1) * θ) - sin ((2 * ↑n + 1) * θ) := by
          rw [hα_cos]
        _ = sin ((2 * ↑(n + 2) + 1) * θ) := by
          have h1 : (2 * (↑n : ℝ) + 1) * θ = (2 * ↑(n + 1) + 1) * θ - 2 * θ := by
            push_cast; ring
          have h2 : (2 * (↑(n + 2) : ℝ) + 1) * θ = (2 * ↑(n + 1) + 1) * θ + 2 * θ := by
            push_cast; ring
          rw [h1, h2]
          exact sin_chebyshev_step (θ := θ) (x := _)


/--
[seqB_sin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem seqB_sin
  {c α θ : ℝ}
-- given
  (hc : c = -cos θ)
  (hα : α = 4 * c ^ 2 - 2) :
-- imply
  ∀ n, sin θ * seqB c α n = sin (2 * (n : ℝ) * θ) := by
-- proof
  have hα_cos : α = 2 * cos (2 * θ) := by rw [hα, hc, cos_two_mul]; ring
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [seqB, Real.sin_zero]
    | 1 =>
      simp only [seqB, hc]
      rw [show 2 * (↑(1 : ℕ) : ℝ) * θ = 2 * θ by push_cast; ring, Real.sin_two_mul]; ring
    | n + 2 =>
      calc
        _ = α * (sin θ * seqB c α (n + 1)) - (sin θ * seqB c α n) := by
          simp only [seqB]
          ring
        _ = α * sin (2 * ↑(n + 1) * θ) - sin (2 * ↑n * θ) := by
          rw [ih (n + 1) (by omega), ih n (by omega)]
        _ = 2 * cos (2 * θ) * sin (2 * ↑(n + 1) * θ) - sin (2 * ↑n * θ) := by rw [hα_cos]
        _ = sin (2 * ↑(n + 2) * θ) := by
          rw [show 2 * (↑n : ℝ) * θ = 2 * ↑(n + 1) * θ - 2 * θ by push_cast; ring,
            show 2 * (↑(n + 2) : ℝ) * θ = 2 * ↑(n + 1) * θ + 2 * θ by push_cast; ring]
          exact sin_chebyshev_step (θ := θ) (x := _)


/--
[seqD_sin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem seqD_sin
  {c α θ : ℝ}
-- given
  (hc : c = -cos θ)
  (hα : α = 4 * c ^ 2 - 2) :
-- imply
  ∀ n, sin θ * seqD c α n = -sin ((2 * (n : ℝ) - 1) * θ) := by
-- proof
  have hα_cos : α = 2 * cos (2 * θ) := by rw [hα, hc, cos_two_mul]; ring
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 =>
      simp only [seqD, mul_one]
      rw [show (2 * (↑(0 : ℕ) : ℝ) - 1) * θ = -(1 * θ) by push_cast; ring, Real.sin_neg]
      ring
    | 1 =>
      simp only [seqD]
      rw [show (2 * (↑(1 : ℕ) : ℝ) - 1) * θ = 1 * θ by push_cast; ring]; ring
    | n + 2 =>
      calc
        _ = α * (sin θ * seqD c α (n + 1)) - (sin θ * seqD c α n) := by
          simp only [seqD]
          ring
        _ = α * (-sin ((2 * ↑(n + 1) - 1) * θ)) - (-sin ((2 * ↑n - 1) * θ)) := by
          rw [ih (n + 1) (by omega), ih n (by omega)]
        _ = -(2 * cos (2 * θ) * sin ((2 * ↑(n + 1) - 1) * θ) -
          sin ((2 * ↑n - 1) * θ)) := by rw [hα_cos]; ring
        _ = -sin ((2 * ↑(n + 2) - 1) * θ) := by
          have h1 : (2 * (↑n : ℝ) - 1) * θ = (2 * ↑(n + 1) - 1) * θ - 2 * θ := by
            push_cast; ring
          have h2 : (2 * (↑(n + 2) : ℝ) - 1) * θ = (2 * ↑(n + 1) - 1) * θ + 2 * θ := by
            push_cast; ring
          rw [h1, h2, sin_chebyshev_step]


/--
[m_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem m_ge_two
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  2 ≤ M.M s t := by
-- proof
  have h1 : M.M s t ≠ 1 := M.off_diagonal s t hst
  omega


/--
[sin_theta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem sin_theta_pos
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  0 < sin (π / (M.M s t : ℝ)) := by
-- proof
  have hm2 := m_ge_two hst hm
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos Real.pi_pos (by positivity)
  ·
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (M.M s t : ℝ))]
    calc
      _ = π * 1 := by ring
      _ < π * (M.M s t : ℝ) := by
        apply mul_lt_mul_of_pos_left _ Real.pi_pos
        exact_mod_cast (show 1 < M.M s t by omega)


/--
[formVal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem formVal_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hm : M.M s t ≠ 0) :
-- imply
  formVal M s t = -cos (π / (M.M s t : ℝ)) := by
-- proof
  simp [formVal, hm]


/--
[seqA_at_m](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem seqA_at_m
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  seqA (formVal M s t) (4 * formVal M s t ^ 2 - 2) (M.M s t) = 1 := by
-- proof
  set c := formVal M s t
  set α := 4 * c ^ 2 - 2
  set m := M.M s t
  set θ := π / (m : ℝ)
  have hc : c = -cos θ := formVal_eq hm
  have hα : α = 4 * c ^ 2 - 2 := rfl
  have hsin_pos : 0 < sin θ := sin_theta_pos hst hm
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hkey := seqA_sin hc hα m
  have hangle : (2 * (m : ℝ) + 1) * θ = θ + 2 * π := by
    simp only [θ]
    field_simp
    ring
  rw [hangle] at hkey
  rw [Real.sin_add_two_pi] at hkey
  exact mul_left_cancel₀ (ne_of_gt hsin_pos) (show sin θ * seqA c α m = sin θ * 1 by linarith)


/--
[seqB_at_m](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem seqB_at_m
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  seqB (formVal M s t) (4 * formVal M s t ^ 2 - 2) (M.M s t) = 0 := by
-- proof
  set c := formVal M s t
  set α := 4 * c ^ 2 - 2
  set m := M.M s t
  set θ := π / (m : ℝ)
  have hc : c = -cos θ := formVal_eq hm
  have hα : α = 4 * c ^ 2 - 2 := rfl
  have hsin_pos : 0 < sin θ := sin_theta_pos hst hm
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hkey := seqB_sin hc hα m
  have hangle : 2 * (m : ℝ) * θ = 2 * π := by
    simp only [θ]
    field_simp
  rw [hangle, Real.sin_two_pi] at hkey
  exact (mul_eq_zero.mp hkey).resolve_left (ne_of_gt hsin_pos)


/--
[seqC_at_m](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem seqC_at_m
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  seqC (formVal M s t) (4 * formVal M s t ^ 2 - 2) (M.M s t) = 0 := by
-- proof
  rw [seqC_eq_neg_seqB, seqB_at_m hst hm, neg_zero]


/--
[seqD_at_m](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem seqD_at_m
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  seqD (formVal M s t) (4 * formVal M s t ^ 2 - 2) (M.M s t) = 1 := by
-- proof
  set c := formVal M s t
  set α := 4 * c ^ 2 - 2
  set m := M.M s t
  set θ := π / (m : ℝ)
  have hc : c = -cos θ := formVal_eq hm
  have hα : α = 4 * c ^ 2 - 2 := rfl
  have hsin_pos : 0 < sin θ := sin_theta_pos hst hm
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hkey := seqD_sin hc hα m
  have hangle : (2 * (m : ℝ) - 1) * θ = 2 * π - θ := by
    simp only [θ]
    field_simp
  rw [hangle, Real.sin_two_pi_sub] at hkey
  have hkey' : sin θ * seqD c α m = sin θ := by linarith
  exact mul_left_cancel₀ (ne_of_gt hsin_pos)
    (show sin θ * seqD c α m = sin θ * 1 by linarith)


/--
[sigma_comp_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem sigma_comp_add_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v₁ v₂ : B → ℝ} :
-- imply
  sigma M s (sigma M t (v₁ + v₂)) = sigma M s (sigma M t v₁) + sigma M s (sigma M t v₂) := by
-- proof
  apply CoxeterGroup.sigma_comp_add M s t v₁ v₂

/--
[sigma_comp_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem sigma_comp_smul_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {c : ℝ}
  {v : B → ℝ} :
-- imply
  sigma M s (sigma M t (c • v)) = c • sigma M s (sigma M t v) := by
-- proof
  apply CoxeterGroup.sigma_comp_smul M s t c v

/--
[iterate_sigma_comp_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem iterate_sigma_comp_add_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {n : ℕ}
  {v₁ v₂ : B → ℝ} :
-- imply
  ((fun w => sigma M s (sigma M t w))^[n]) (v₁ + v₂) = ((fun w => sigma M s (sigma M t w))^[n]) v₁ + ((fun w => sigma M s (sigma M t w))^[n]) v₂ := by
-- proof
  apply CoxeterGroup.iterate_sigma_comp_add M s t n v₁ v₂

/--
[iterate_sigma_comp_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem iterate_sigma_comp_smul_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {n : ℕ}
  {c : ℝ}
  {v : B → ℝ} :
-- imply
  ((fun w => sigma M s (sigma M t w))^[n]) (c • v) = c • ((fun w => sigma M s (sigma M t w))^[n]) v := by
-- proof
  apply CoxeterGroup.iterate_sigma_comp_smul M s t n c v

/--
[iterate_sigma_comp_fixes_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem iterate_sigma_comp_fixes_orthogonal_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {n : ℕ}
  {w : B → ℝ}
-- given
  (hs : bilinForm M w (e s) = 0)
  (ht : bilinForm M w (e t) = 0) :
-- imply
  ((fun v => sigma M s (sigma M t v))^[n]) w = w := by
-- proof
  apply CoxeterGroup.iterate_sigma_comp_fixes_orthogonal M s t n w hs ht

/--
[seqAB_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem seqAB_step_eq
  [DecidableEq B]
  [Fintype B]
  {c : ℝ} :
-- imply
  ∀ n, seqA c (4 * c ^ 2 - 2) (n + 1) = (4 * c ^ 2 - 1) * seqA c (4 * c ^ 2 - 2) n + 2 * c * seqB c (4 * c ^ 2 - 2) n ∧ seqB c (4 * c ^ 2 - 2) (n + 1) = -2 * c * seqA c (4 * c ^ 2 - 2) n - seqB c (4 * c ^ 2 - 2) n := by
-- proof
  apply CoxeterGroup.seqAB_step c

/--
[seqCD_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem seqCD_step_eq
  [DecidableEq B]
  [Fintype B]
  {c : ℝ} :
-- imply
  ∀ n, seqC c (4 * c ^ 2 - 2) (n + 1) = (4 * c ^ 2 - 1) * seqC c (4 * c ^ 2 - 2) n + 2 * c * seqD c (4 * c ^ 2 - 2) n ∧ seqD c (4 * c ^ 2 - 2) (n + 1) = -2 * c * seqC c (4 * c ^ 2 - 2) n - seqD c (4 * c ^ 2 - 2) n := by
-- proof
  apply CoxeterGroup.seqCD_step c

/--
[iter_e_s_formula_fn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem iter_e_s_formula_fn_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {n : ℕ} :
-- imply
  ((fun w => sigma M s (sigma M t w))^[n]) (e s) = seqA (formVal M s t) (4 * formVal M s t ^ 2 - 2) n • e s + seqB (formVal M s t) (4 * formVal M s t ^ 2 - 2) n • e t := by
-- proof
  apply CoxeterGroup.iter_e_s_formula_fn M s t n

/--
[iter_e_s_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem iter_e_s_formula_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {n : ℕ}
  {u : B} :
-- imply
  let c := formVal M s t
  let α := 4 * c ^ 2 - 2
  ((fun w => sigma M s (sigma M t w))^[n]) (e s) u = seqA c α n * e s u + seqB c α n * e t u := by
-- proof
  apply CoxeterGroup.iter_e_s_formula M s t n u

/--
[iter_e_t_formula_fn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem iter_e_t_formula_fn_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {n : ℕ} :
-- imply
  ((fun w => sigma M s (sigma M t w))^[n]) (e t) = seqC (formVal M s t) (4 * formVal M s t ^ 2 - 2) n • e s + seqD (formVal M s t) (4 * formVal M s t ^ 2 - 2) n • e t := by
-- proof
  apply CoxeterGroup.iter_e_t_formula_fn M s t n

/--
[iter_e_t_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean)
-/
@[path]
public theorem iter_e_t_formula_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {n : ℕ}
  {u : B} :
-- imply
  let c := formVal M s t
  let α := 4 * c ^ 2 - 2
  ((fun w => sigma M s (sigma M t w))^[n]) (e t) u = seqC c α n * e s u + seqD c α n * e t u := by
-- proof
  apply CoxeterGroup.iter_e_t_formula M s t n u


-- created on 2026-10-23
-- updated on 2026-10-26
