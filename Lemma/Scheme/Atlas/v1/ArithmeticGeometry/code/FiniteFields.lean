import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.FiniteFields
open Finset MvPolynomial
open MvPolynomial


/--
[finite_subgroup_of_field_isCyclic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma finite_subgroup_of_field_isCyclic
  {k : Type*}
  [Field k]
  {G : Subgroup kˣ}
  [Finite G] :
-- imply
  IsCyclic G :=
-- proof
  isCyclic_subgroup_units G
open Finset

/--
[card_filter_quadraticChar_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma card_filter_quadraticChar_neg_one
  {F : Type*}
  [Field F]
  [Fintype F]
  [DecidableEq F]
-- given
  (hF : ringChar F ≠ 2) :
-- imply
  (univ.filter fun a : F => (quadraticChar F) a = -1).card = (Fintype.card F - 1) / 2 := by
-- proof
  set χ := quadraticChar F with hχ_def
  set Spos := univ.filter fun a : F => χ a = 1
  set Sneg := univ.filter fun a : F => χ a = -1
  set Szero := univ.filter fun a : F => χ a = 0
  have hSzero_eq : Szero = {(0 : F)} := by
    ext a; simp only [Szero, mem_filter, mem_univ, true_and, mem_singleton]
    exact quadraticChar_eq_zero_iff
  have hpart' : univ (α := F) = Szero ∪ (Spos ∪ Sneg) := by
    ext a; simp only [Szero, Spos, Sneg, mem_union, mem_filter, mem_univ, true_and]
    obtain h | h | h <;> simp [show χ a = _ from h] := quadraticChar_isQuadratic F a
  have hdzp : Disjoint Szero Spos := disjoint_filter.mpr fun a _ h0 h1 => by linarith
  have hdzn : Disjoint Szero Sneg := disjoint_filter.mpr fun a _ h0 h1 => by linarith
  have hdpn : Disjoint Spos Sneg := disjoint_filter.mpr fun a _ h1 hm1 => by linarith
  have hdzpn : Disjoint Szero (Spos ∪ Sneg) := disjoint_union_right.mpr ⟨hdzp, hdzn⟩
  have hcard_sum : Spos.card + Sneg.card = Fintype.card F - 1 := by
    have h := card_univ (α := F)
    rw [hpart', card_union_of_disjoint hdzpn, card_union_of_disjoint hdpn,
      hSzero_eq, card_singleton] at h; omega
  have hsum_diff : (Spos.card : ℤ) - Sneg.card = 0 := by
    have hsum : ∑ a : F, χ a = 0 := quadraticChar_sum_zero hF
    rw [show (∑ a : F, χ a) = ∑ a ∈ univ, χ a from rfl, hpart'] at hsum
    rw [sum_union hdzpn, sum_union hdpn] at hsum
    have h0 : ∑ a ∈ Szero, χ a = 0 := by
      rw [hSzero_eq, sum_singleton]; exact quadraticChar_zero
    have h1 : ∑ a ∈ Spos, χ a = (Spos.card : ℤ) := by
      rw [show ∑ a ∈ Spos, χ a = ∑ _ ∈ Spos, (1 : ℤ) from
        sum_congr rfl fun a ha => by simp [Spos] at ha; exact ha]; simp
    have hm1 : ∑ a ∈ Sneg, χ a = -(Sneg.card : ℤ) := by
      rw [show ∑ a ∈ Sneg, χ a = ∑ _ ∈ Sneg, (-1 : ℤ) from
        sum_congr rfl fun a ha => by simp [Sneg] at ha; exact ha]; simp
    linarith
  omega

/--
[phi_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma phi_injective
  [Field F]
  {α β : F}
  {a₁ a₂ : F}
-- given
  (hαβ : α ≠ β)
  (hβ₁ : β + a₁ ≠ 0)
  (hβ₂ : β + a₂ ≠ 0)
  (h : (α + a₁) * (β + a₁)⁻¹ = (α + a₂) * (β + a₂)⁻¹) :
-- imply
  a₁ = a₂ := by
-- proof
  have h1 : (α + a₁) / (β + a₁) = (α + a₂) / (β + a₂) := by
    rwa [div_eq_mul_inv, div_eq_mul_inv]
  rw [div_eq_div_iff hβ₁ hβ₂] at h1
  have h2 : (α - β) * (a₂ - a₁) = 0 := by
    have : (α - β) * (a₂ - a₁) = (α + a₁) * (β + a₂) - (α + a₂) * (β + a₁) := by ring
    rw [this, h1, sub_self]
  exact (sub_eq_zero.mp
    (or_iff_not_imp_left.mp (mul_eq_zero.mp h2) (sub_ne_zero.mpr hαβ))).symm

/--
[rabin_different_type_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma rabin_different_type_count
  {F : Type*}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {α β : F}
-- given
  (hF : ringChar F ≠ 2)
  (hαβ : α ≠ β) :
-- imply
  (univ.filter fun δ : F => α + δ ≠ 0 ∧ β + δ ≠ 0 ∧ (quadraticChar F) (α + δ) ≠ (quadraticChar F) (β + δ)).card = (Fintype.card F - 1) / 2 := by
-- proof
  set S := univ.filter fun δ : F =>
    α + δ ≠ 0 ∧ β + δ ≠ 0 ∧ (quadraticChar F) (α + δ) ≠ (quadraticChar F) (β + δ)
  set T := univ.filter fun γ : F => (quadraticChar F) γ = -1
  suffices hST : S.card = T.card by rw [hST]; exact card_filter_quadraticChar_neg_one F hF
  apply card_bij (fun δ _ => (α + δ) * (β + δ)⁻¹)
  ·
    intro δ hδ
    simp only [S, mem_filter, mem_univ, true_and] at hδ
    obtain ⟨hα, hβ, hne⟩ := hδ
    simp only [T, mem_filter, mem_univ, true_and]
    rw [map_mul]
    have hχbinv : (quadraticChar F) (β + δ)⁻¹ = (quadraticChar F) (β + δ) := by
      have hmul1 : (quadraticChar F) (β + δ) * (quadraticChar F) (β + δ)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hβ]; exact MulChar.map_one _
      obtain h0 | h1 | hm1 := quadraticChar_isQuadratic F (β + δ)
      · exact absurd (quadraticChar_eq_zero_iff.mp h0) hβ
      all_goals rcases quadraticChar_isQuadratic F (β + δ)⁻¹ with h0' | h1' | hm1'
      · exact absurd (quadraticChar_eq_zero_iff.mp h0') (inv_ne_zero hβ)
      · rw [h1, h1']
      · rw [h1, hm1'] at hmul1; norm_num at hmul1
      · exact absurd (quadraticChar_eq_zero_iff.mp h0') (inv_ne_zero hβ)
      · rw [hm1, h1'] at hmul1; norm_num at hmul1
      · rw [hm1, hm1']
    rw [hχbinv]
    obtain h0 | h1 | hm1 := quadraticChar_isQuadratic F (α + δ)
    · exact absurd (quadraticChar_eq_zero_iff.mp h0) hα
    all_goals rcases quadraticChar_isQuadratic F (β + δ) with h0' | h1' | hm1'
    · exact absurd (quadraticChar_eq_zero_iff.mp h0') hβ
    · exact absurd (h1 ▸ h1' ▸ rfl) hne
    · simp [h1, hm1']
    · exact absurd (quadraticChar_eq_zero_iff.mp h0') hβ
    · simp [hm1, h1']
    · exact absurd (hm1 ▸ hm1' ▸ rfl) hne
  ·
    intro a₁ ha₁ a₂ ha₂ h
    simp only [S, mem_filter, mem_univ, true_and] at ha₁ ha₂
    exact phi_injective hαβ ha₁.2.1 ha₂.2.1 h
  ·
    intro γ hγ
    simp only [T, mem_filter, mem_univ, true_and] at hγ
    have hγne0 : γ ≠ 0 := by
      intro h; rw [h, quadraticChar_zero] at hγ; norm_num at hγ
    have hγne1 : γ ≠ 1 := by
      intro h; rw [h, MulChar.map_one] at hγ; norm_num at hγ
    have h1γ : (1 : F) - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγne1)
    have hba : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ)
    refine ⟨(γ * β - α) * (1 - γ)⁻¹, ?_, ?_⟩
    ·
      simp only [S, mem_filter, mem_univ, true_and]
      have hβδ : β + (γ * β - α) * (1 - γ)⁻¹ = (β - α) * (1 - γ)⁻¹ := by
        rw [eq_comm, ← sub_eq_zero]; field_simp; ring
      have hαδ : α + (γ * β - α) * (1 - γ)⁻¹ = γ * (β - α) * (1 - γ)⁻¹ := by
        rw [eq_comm, ← sub_eq_zero]; field_simp; ring
      refine ⟨?_, ?_, ?_⟩
      ·
        rw [hαδ]; exact mul_ne_zero (mul_ne_zero hγne0 hba) (inv_ne_zero h1γ)
      ·
        rw [hβδ]; exact mul_ne_zero hba (inv_ne_zero h1γ)
      ·
        rw [hαδ, hβδ,
          show γ * (β - α) * (1 - γ)⁻¹ = γ * ((β - α) * (1 - γ)⁻¹) from by ring,
          map_mul]
        intro heq
        have hcne0 : (quadraticChar F) ((β - α) * (1 - γ)⁻¹) ≠ 0 := by
          rw [Ne, quadraticChar_eq_zero_iff]
          exact mul_ne_zero hba (inv_ne_zero h1γ)
        obtain h0 | h1 | hm1 := quadraticChar_isQuadratic F ((β - α) * (1 - γ)⁻¹)
        · exact hcne0 h0
        · rw [h1, hγ] at heq; norm_num at heq
        · rw [hm1, hγ] at heq; norm_num at heq
    ·
      have hβδ : β + (γ * β - α) * (1 - γ)⁻¹ = (β - α) * (1 - γ)⁻¹ := by
        rw [eq_comm, ← sub_eq_zero]; field_simp; ring
      have hαδ : α + (γ * β - α) * (1 - γ)⁻¹ = γ * (β - α) * (1 - γ)⁻¹ := by
        rw [eq_comm, ← sub_eq_zero]; field_simp; ring
      rw [hαδ, hβδ]; field_simp
open MvPolynomial

/--
[eval_diagonal_quadratic_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma eval_diagonal_quadratic_form
  [Field K]
  {a b c : K}
  {v : Fin 3 → K} :
-- imply
  eval v (C a * X 0 ^ 2 + C b * X 1 ^ 2 + C c * X 2 ^ 2 : MvPolynomial (Fin 3) K) = a * (v 0) ^ 2 + b * (v 1) ^ 2 + c * (v 2) ^ 2 := by
-- proof
  simp only [map_add, map_mul, map_pow, eval_C, eval_X]
set_option maxHeartbeats 800000 in

/--
[conic_has_rational_point_of_finite_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma conic_has_rational_point_of_finite_field
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {a b c : K}
-- given
  (hodd : ringChar K ≠ 2)
  (_ha : a ≠ 0)
  (_hb : b ≠ 0)
  (_hc : c ≠ 0) :
-- imply
  ∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
-- proof
  set p := ringChar K
  haveI : CharP K p := ringChar.charP K
  have hp_prime : Nat.Prime p := by
    obtain hp | h0 := CharP.char_is_prime_or_zero K p
    · exact hp
    · exact absurd h0 (CharP.ringChar_ne_zero_of_finite K)
  have hp_ge : p ≥ 3 := by have := hp_prime.two_le; omega
  have hdeg : (C a * X 0 ^ 2 + C b * X 1 ^ 2 + C c * X 2 ^ 2 :
    MvPolynomial (Fin 3) K).totalDegree ≤ 2 := by
    apply le_trans (totalDegree_add _ _)
    simp only [sup_le_iff]
    exact ⟨le_trans (totalDegree_add _ _) (by
      simp only [sup_le_iff]
      exact ⟨le_trans (totalDegree_mul _ _) (by simp [totalDegree_C, totalDegree_X_pow]),
        le_trans (totalDegree_mul _ _) (by simp [totalDegree_C, totalDegree_X_pow])⟩),
      le_trans (totalDegree_mul _ _) (by simp [totalDegree_C, totalDegree_X_pow])⟩
  have hdeg_lt : (C a * X 0 ^ 2 + C b * X 1 ^ 2 + C c * X 2 ^ 2 :
    MvPolynomial (Fin 3) K).totalDegree < Fintype.card (Fin 3) := by
    simp only [Fintype.card_fin]; omega
  have hcw := char_dvd_card_solutions p hdeg_lt
  have hzero_sol : eval (fun _ : Fin 3 => (0 : K))
    (C a * X 0 ^ 2 + C b * X 1 ^ 2 + C c * X 2 ^ 2 : MvPolynomial (Fin 3) K) = 0 := by
    rw [eval_diagonal_quadratic_form]; ring
  have hcard_pos : 0 < Fintype.card { x : Fin 3 → K //
    eval x (C a * X 0 ^ 2 + C b * X 1 ^ 2 + C c * X 2 ^ 2) = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨fun _ => 0, hzero_sol⟩⟩
  have hcard_gt_one : 1 < Fintype.card { x : Fin 3 → K //
    eval x (C a * X 0 ^ 2 + C b * X 1 ^ 2 + C c * X 2 ^ 2) = 0 } := by
    obtain ⟨k, hk⟩ := hcw
    rw [hk] at hcard_pos ⊢
    nlinarith [Nat.pos_of_mul_pos_left hcard_pos]
  rw [Fintype.one_lt_card_iff] at hcard_gt_one
  obtain ⟨⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩, hne⟩ := hcard_gt_one
  have hne_val : v₁ ≠ v₂ := fun h => hne (Subtype.ext h)
  by_cases h₁ : v₁ = fun _ => 0
  ·
    have hv₂_ne : v₂ ≠ fun _ => 0 := fun h₂ => hne_val (by rw [h₁, h₂])
    obtain ⟨i, hi⟩ : ∃ i, v₂ i ≠ 0 := by
      by_contra h; push Not at h; exact hv₂_ne (funext h)
    exact ⟨v₂ 0, v₂ 1, v₂ 2, by fin_cases i <;> simp_all,
      by rw [← eval_diagonal_quadratic_form]; exact hv₂⟩
  ·
    obtain ⟨i, hi⟩ : ∃ i, v₁ i ≠ 0 := by
      by_contra h; push Not at h; exact h₁ (funext h)
    exact ⟨v₁ 0, v₁ 1, v₁ 2, by fin_cases i <;> simp_all,
      by rw [← eval_diagonal_quadratic_form]; exact hv₁⟩

/--
[diag_binary_form_trivial_of_not_square](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma diag_binary_form_trivial_of_not_square
  [Field K]
  {a b : K}
  {x y : K}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hnsq : ¬IsSquare (-b * a⁻¹))
  (heq : a * x ^ 2 + b * y ^ 2 = 0) :
-- imply
  x = 0 ∧ y = 0 := by
-- proof
  constructor
  · by_contra hx
    by_cases hy : y = 0
    · have h1 : a * x ^ 2 = 0 := by subst hy; linear_combination heq
      exact hx (sq_eq_zero_iff.mp ((mul_eq_zero.mp h1).resolve_left ha))
    · exact absurd ⟨x * y⁻¹, by
      have h1 : a * x ^ 2 = -(b * y ^ 2) := by linear_combination heq
      field_simp; linear_combination -h1⟩ hnsq
  · by_contra hy
    by_cases hx : x = 0
    · have h1 : b * y ^ 2 = 0 := by subst hx; linear_combination heq
      exact hy (sq_eq_zero_iff.mp ((mul_eq_zero.mp h1).resolve_left hb))
    · exact absurd ⟨x * y⁻¹, by
      have h1 : a * x ^ 2 = -(b * y ^ 2) := by linear_combination heq
      field_simp; linear_combination -h1⟩ hnsq

/--
[quadChar_jacobi_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma quadChar_jacobi_sum
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
-- given
  (hodd : ringChar K ≠ 2) :
-- imply
  ∑ a : K, (quadraticChar K) (a * (a - 1)) = -1 := by
-- proof
  set χ := quadraticChar K with hχ_def
  simp_rw [map_mul χ, show ∀ a : K, a - 1 = -1 * (1 - a) from fun a => by ring, map_mul χ]
  simp_rw [← mul_assoc, mul_comm (χ _) (χ (-1)), mul_assoc, ← Finset.mul_sum]
  change χ (-1) * jacobiSum χ χ = -1
  have hχ_inv : χ⁻¹ = χ := by
    have hsq := (quadraticChar_isQuadratic K).sq_eq_one
    rw [sq, mul_eq_one_iff_eq_inv] at hsq; exact hsq.symm
  rw [show jacobiSum χ χ = jacobiSum χ χ⁻¹ from by rw [hχ_inv]]
  rw [jacobiSum_nontrivial_inv (quadraticChar_ne_one hodd)]
  nlinarith [quadraticChar_sq_one (F := K) (neg_ne_zero.mpr one_ne_zero)]

/--
[quadChar_sum_sq_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma quadChar_sum_sq_add
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {d : K}
-- given
  (hodd : ringChar K ≠ 2)
  (hd : d ≠ 0) :
-- imply
  ∑ t : K, (quadraticChar K) (t ^ 2 + d) = -1 := by
-- proof
  set χ := quadraticChar K with hχ_def
  suffices key : ∑ u : K, χ (u * (u - d)) = -1 by
    suffices eq : ∑ t : K, χ (t ^ 2 + d) = ∑ u : K, χ (u * (u - d)) by rw [eq, key]
    have fubini : ∑ t : K, χ (t ^ 2 + d) =
      ∑ u : K, ↑(Finset.univ.filter (fun t : K => t ^ 2 = u)).card * χ (u + d) := by
      have h := Finset.sum_fiberwise_of_maps_to (g := fun t : K => t ^ 2)
        (t := Finset.univ) (s := Finset.univ) (by simp) (fun t => χ (t ^ 2 + d))
      rw [← h]; congr 1; ext u
      trans (∑ _i ∈ Finset.univ.filter (fun t : K => t ^ 2 = u), χ (u + d))
      · exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
      · rw [Finset.sum_const, nsmul_eq_mul]
    have fiber_eq : ∀ u : K,
      (↑(Finset.univ.filter (fun t : K => t ^ 2 = u)).card : ℤ) = χ u + 1 := by
      intro u
      have hfin : Finset.univ.filter (fun t : K => t ^ 2 = u) =
        {x : K | x ^ 2 = u}.toFinset := by
        ext x; simp [Finset.mem_filter]
      rw [hfin]; exact quadraticChar_card_sqrts hodd u
    rw [fubini]; simp_rw [fiber_eq, add_mul, one_mul]; rw [Finset.sum_add_distrib]
    have sum_shift : ∑ u : K, χ (u + d) = 0 := by
      have : ∑ u : K, χ (u + d) = ∑ v : K, χ v :=
        Fintype.sum_equiv (Equiv.addRight d) _ _ (fun _ => rfl)
      rw [this]; exact quadraticChar_sum_zero hodd
    rw [sum_shift, add_zero]
    simp_rw [← map_mul χ]
    exact Fintype.sum_equiv (Equiv.addRight d) _ _ (fun u => by
      show χ (u * (u + d)) = χ ((u + d) * ((u + d) - d)); congr 1; ring)
  have subst_eq : ∑ u : K, χ (u * (u - d)) = ∑ a : K, χ (a * (a - 1)) := by
    symm
    exact Fintype.sum_equiv (Equiv.mulLeft₀ d hd) _ _ (fun a => by
      show χ (a * (a - 1)) = χ (d * a * (d * a - d))
      have h : d * a * (d * a - d) = d ^ 2 * (a * (a - 1)) := by ring
      rw [h, map_mul χ (d ^ 2) _, map_pow, quadraticChar_sq_one hd, one_mul])
  rw [subst_eq]
  exact quadChar_jacobi_sum K hodd

/--
[quadChar_sum_ec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma quadChar_sum_ec
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {e c : K}
-- given
  (hodd : ringChar K ≠ 2)
  (he : e ≠ 0)
  (hc : c ≠ 0) :
-- imply
  ∑ z : K, (quadraticChar K) (e + c * z ^ 2) = -(quadraticChar K) c := by
-- proof
  set χ := quadraticChar K
  have factor : ∀ z : K, e + c * z ^ 2 = c * (e * c⁻¹ + z ^ 2) := fun z => by field_simp
  simp_rw [factor, map_mul χ, ← Finset.mul_sum]
  have hec : e * c⁻¹ ≠ 0 := mul_ne_zero he (inv_ne_zero hc)
  simp_rw [show ∀ z : K, e * c⁻¹ + z ^ 2 = z ^ 2 + e * c⁻¹ from fun z => by ring]
  rw [quadChar_sum_sq_add K hodd _ hec]; ring

/--
[fiber_card_chi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma fiber_card_chi
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {a d : K}
-- given
  (hodd : ringChar K ≠ 2)
  (ha : a ≠ 0) :
-- imply
  (Fintype.card { x : K // a * x ^ 2 + d = 0 } : ℤ) = 1 + (quadraticChar K) (-d * a⁻¹) := by
-- proof
  have equiv : { x : K // a * x ^ 2 + d = 0 } ≃ { x : K // x ^ 2 = -d * a⁻¹ } := by
    refine Equiv.subtypeEquiv (Equiv.refl K) (fun x => ?_)
    simp only [Equiv.refl_apply]
    rw [show -d * a⁻¹ = -d / a from by rw [div_eq_mul_inv]]
    rw [eq_div_iff ha]
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  rw [Fintype.card_congr equiv]
  have h := quadraticChar_card_sqrts hodd (-d * a⁻¹)
  have card_eq : (Fintype.card { x : K // x ^ 2 = -d * a⁻¹ } : ℤ) =
    ↑(({x : K | x ^ 2 = -d * a⁻¹}.toFinset).card) := by
    norm_cast; simp only [Set.toFinset_setOf]; exact Fintype.card_subtype _
  rw [card_eq, h]; ring

/--
[double_sum_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma double_sum_vanish
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {b c : K}
-- given
  (hodd : ringChar K ≠ 2)
  (hb : b ≠ 0)
  (hc : c ≠ 0) :
-- imply
  ∑ y : K, ∑ z : K, (quadraticChar K) (b * y ^ 2 + c * z ^ 2) = 0 := by
-- proof
  set χ := quadraticChar K
  set q := Fintype.card K
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : K))]
  simp only [mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_add]
  have h_csq : ∑ z : K, χ (c * z ^ 2) = χ c * ((q : ℤ) - 1) := by
    simp_rw [map_mul χ, ← Finset.mul_sum]; congr 1
    have hval : ∀ z : K, χ (z ^ 2) = if z = 0 then 0 else 1 := by
      intro z; by_cases hz : z = 0
      · subst hz; simp [MulChar.map_zero]
      · simp only [hz, if_false]; rw [map_pow, quadraticChar_sq_one hz]
    simp_rw [hval]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Finset.univ.filter (fun z : K => ¬z = 0)).card = q - 1 := by
      rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    rw [this]; have hpos : 1 ≤ q := Fintype.card_pos; omega
  rw [h_csq]
  have h_nonzero : ∀ y ∈ Finset.univ.erase (0 : K),
    ∑ z : K, χ (b * y ^ 2 + c * z ^ 2) = -χ c := by
    intro y hy; rw [Finset.mem_erase] at hy
    exact quadChar_sum_ec K hodd (b * y ^ 2) c (mul_ne_zero hb (pow_ne_zero 2 hy.1)) hc
  rw [Finset.sum_congr rfl h_nonzero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.erase (0 : K)).card = q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  rw [hcard]; have hpos : 1 ≤ q := Fintype.card_pos
  push_cast [Nat.cast_sub hpos]; ring

/--
[affineSolCount_irred_char2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma affineSolCount_irred_char2
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  [CharP K 2]
  {a b c : K}
-- given
  (_ha : a ≠ 0)
  (hb : b ≠ 0)
  (_hc : c ≠ 0) :
-- imply
  affineSolCount K a b c = (Fintype.card K) ^ 2 := by
-- proof
  unfold affineSolCount
  have hsq_inj : Function.Injective (fun x : K => x ^ 2) := (bijective_frobenius K 2).1
  have hsq_surj : Function.Surjective (fun x : K => x ^ 2) := (bijective_frobenius K 2).2
  rw [show (Fintype.card K) ^ 2 = Fintype.card K * Fintype.card K from by ring,
    ← Fintype.card_prod]
  apply Fintype.card_congr
  refine Equiv.ofBijective (fun ⟨v, _⟩ => (v 2, v 0)) ⟨?_, ?_⟩
  ·
    intro ⟨v, hv⟩ ⟨w, hw⟩ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hz, hx⟩ := heq
    have hy_sq : (v 1) ^ 2 = (w 1) ^ 2 := by
      have h1 : b * (v 1) ^ 2 = b * (w 1) ^ 2 := by
        have hsub : a * (v 0) ^ 2 + b * (v 1) ^ 2 + c * (v 2) ^ 2 -
          (a * (w 0) ^ 2 + b * (w 1) ^ 2 + c * (w 2) ^ 2) = 0 := by
          rw [hv, hw, sub_self]
        rw [hx, hz] at hsub
        have : b * (v 1) ^ 2 - b * (w 1) ^ 2 = 0 := by linear_combination hsub
        exact sub_eq_zero.mp this
      exact mul_left_cancel₀ hb h1
    have hy : v 1 = w 1 := hsq_inj hy_sq
    exact Subtype.ext (funext fun i => by fin_cases i <;> [exact hx; exact hy; exact hz])
  ·
    intro ⟨z, x⟩
    obtain ⟨y, hy⟩ := hsq_surj (-(a * x ^ 2 + c * z ^ 2) * b⁻¹)
    have hby : b * y ^ 2 = -(a * x ^ 2 + c * z ^ 2) := by
      have : y ^ 2 = -(a * x ^ 2 + c * z ^ 2) * b⁻¹ := hy
      rw [this]; field_simp
    refine ⟨⟨![x, y, z], ?_⟩, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      show a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0
      rw [hby]; ring
    · simp [Matrix.cons_val_zero]
set_option maxHeartbeats 400000 in

/--
[affineSolCount_irred_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma affineSolCount_irred_odd
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {a b c : K}
-- given
  (hodd : ringChar K ≠ 2)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0) :
-- imply
  affineSolCount K a b c = (Fintype.card K) ^ 2 := by
-- proof
  unfold affineSolCount
  set q := Fintype.card K
  suffices key : (Fintype.card { v : Fin 3 → K //
    a * (v 0) ^ 2 + b * (v 1) ^ 2 + c * (v 2) ^ 2 = 0 } : ℤ) = (q ^ 2 : ℤ) by
    exact_mod_cast key
  rw [Fintype.card_congr (fiberEquivOdd K a b c), Fintype.card_sigma]
  push_cast
  simp_rw [fiber_card_chi K hodd a _ ha]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [show (Fintype.card (K × K) : ℤ) = (q : ℤ) ^ 2 from by
    rw [Fintype.card_prod]; push_cast; ring]
  suffices h : ∑ p : K × K,
    (quadraticChar K) (-(b * p.1 ^ 2 + c * p.2 ^ 2) * a⁻¹) = 0 by
    linarith
  simp_rw [show ∀ p : K × K, -(b * p.1 ^ 2 + c * p.2 ^ 2) * a⁻¹ =
    (-a⁻¹) * (b * p.1 ^ 2 + c * p.2 ^ 2) from fun p => by ring]
  simp_rw [map_mul (quadraticChar K), ← Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  rw [double_sum_vanish K hodd b c hb hc, mul_zero]

/--
[affineSolCount_irred](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma affineSolCount_irred
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {a b c : K}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0) :
-- imply
  affineSolCount K a b c = (Fintype.card K) ^ 2 := by
-- proof
  obtain h2 | hodd := eq_or_ne (ringChar K) 2
  ·
    haveI : CharP K 2 := by rw [← h2]; exact ringChar.charP K
    exact affineSolCount_irred_char2 K a b c ha hb hc
  ·
    exact affineSolCount_irred_odd K hodd a b c ha hb hc
set_option maxRecDepth 2048 in

/--
[affineSolCount_double_line_char2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma affineSolCount_double_line_char2
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  [CharP K 2]
  {a b : K}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  affineSolCount K a b 0 = (Fintype.card K) ^ 2 := by
-- proof
  unfold affineSolCount
  have hsq_surj : Function.Surjective (fun x : K => x ^ 2) := (bijective_frobenius K 2).2
  obtain ⟨d, hd_eq⟩ := hsq_surj (b * a⁻¹)
  simp only at hd_eq
  have hbd : b = a * d ^ 2 := by rw [hd_eq]; field_simp
  have hd_ne : d ≠ 0 := by
    intro hd0; rw [hd0, sq, mul_zero, mul_zero] at hbd; exact hb hbd
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have char2_sq : ∀ x y : K, (x + d * y) ^ 2 = x ^ 2 + d ^ 2 * y ^ 2 := by
    intro x y
    have : (x + d * y) ^ 2 = x ^ 2 + 2 * (x * (d * y)) + (d * y) ^ 2 := by ring
    rw [this, h2K]; ring
  have hform : ∀ v : Fin 3 → K,
    (a * (v 0) ^ 2 + b * (v 1) ^ 2 + 0 * (v 2) ^ 2 = 0) ↔ v 0 = d * v 1 := by
    intro v; constructor
    · intro hv
      have hv' : a * (v 0) ^ 2 + a * d ^ 2 * (v 1) ^ 2 = 0 := by
        rw [← hbd]; linear_combination hv
      have h1 : a * ((v 0) ^ 2 + d ^ 2 * (v 1) ^ 2) = 0 := by linear_combination hv'
      have h2 : (v 0) ^ 2 + d ^ 2 * (v 1) ^ 2 = 0 := (mul_eq_zero.mp h1).resolve_left ha
      have h3 : (v 0 + d * v 1) ^ 2 = 0 := by rw [char2_sq]; linear_combination h2
      have h4 : v 0 + d * v 1 = 0 := sq_eq_zero_iff.mp h3
      have heq : v 0 = -(d * v 1) := by linear_combination h4
      rw [heq]; exact (neg_eq_of_add_eq_zero_left (CharTwo.add_self_eq_zero (d * v 1)))
    · intro hv0; rw [hv0, hbd]
      have : a * (d * v 1) ^ 2 + a * d ^ 2 * v 1 ^ 2 + 0 * v 2 ^ 2 =
        a * d ^ 2 * v 1 ^ 2 * 2 := by ring
      rw [this, h2K]; ring
  rw [show (Fintype.card K) ^ 2 = Fintype.card K * Fintype.card K from by ring,
    ← Fintype.card_prod]
  apply Fintype.card_congr
  refine Equiv.ofBijective (fun ⟨v, hv⟩ => (v 1, v 2)) ⟨?_, ?_⟩
  · intro ⟨v, hv⟩ ⟨w, hw⟩ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hy, hz⟩ := heq
    have hv0 := (hform v).mp hv
    have hw0 := (hform w).mp hw
    apply Subtype.ext; funext i; fin_cases i
    · show v 0 = w 0; rw [hv0, hw0, hy]
    · exact hy
    · exact hz
  · intro ⟨y, z⟩
    exact ⟨⟨![d * y, y, z], (hform _).mpr
      (by simp [Matrix.cons_val_zero, Matrix.cons_val_one])⟩,
      by simp only [Prod.mk.injEq]
        exact ⟨by simp [Matrix.cons_val_one],
          by simp [Matrix.cons_val_two, Matrix.head_cons]⟩⟩

/--
[affineSolCount_split_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma affineSolCount_split_base
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {a b : K}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hsq : IsSquare (-b * a⁻¹))
  (hchar : ringChar K ≠ 2) :
-- imply
  affineSolCount K a b 0 = 2 * (Fintype.card K) ^ 2 - Fintype.card K := by
-- proof
  classical
  unfold affineSolCount
  obtain ⟨d, hd_sq⟩ := hsq
  have hbd : b = -(a * d ^ 2) := by
    have h : -b * a⁻¹ = d ^ 2 := by rw [hd_sq]; ring
    have h2 : -b = d ^ 2 * a := by
      calc -b = -b * a⁻¹ * a := by rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]
        _ = d ^ 2 * a := by rw [h]
    linear_combination -h2
  have hd : d ≠ 0 := by
    intro hd; rw [hd, sq, mul_zero, mul_zero, neg_zero] at hbd; exact hb hbd
  have hfact : ∀ x y : K, a * x ^ 2 + b * y ^ 2 = a * (x - d * y) * (x + d * y) := by
    intro x y; rw [hbd]; ring
  have h2K : (2 : K) ≠ 0 := by
    haveI : CharP K (ringChar K) := ringChar.charP K
    obtain hp | h0 := CharP.char_is_prime_or_zero K (ringChar K)
    · intro h2
      have h2' : (ringChar K) ∣ 2 :=
        (CharP.cast_eq_zero_iff K (ringChar K) 2).mp (by exact_mod_cast h2)
      exact hchar (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h2') hp.two_le)
    · exact absurd h0 (CharP.ringChar_ne_zero_of_finite K)
  set q := Fintype.card K
  rw [Fintype.card_subtype]
  set L1 := (univ : Finset (Fin 3 → K)).filter (fun v => v 0 = d * v 1)
  set L2 := (univ : Finset (Fin 3 → K)).filter (fun v => v 0 = -(d * v 1))
  have hfilt : (univ.filter (fun v : Fin 3 → K =>
    a * (v 0) ^ 2 + b * (v 1) ^ 2 + 0 * (v 2) ^ 2 = 0)) = L1 ∪ L2 := by
    rw [← filter_or]
    apply filter_congr
    intro v _
    constructor
    · intro heq
      have heq0 : a * (v 0) ^ 2 + b * (v 1) ^ 2 = 0 := by linear_combination heq
      rw [hfact] at heq0
      obtain h1 | h1 := mul_eq_zero.mp heq0
      · exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left ha))
      · exact Or.inr (by linear_combination h1)
    · rintro (h1 | h1) <;> (rw [h1, hbd]; ring)
  rw [hfilt]
  have hline : ∀ c : K, ((univ : Finset (Fin 3 → K)).filter (fun v => v 0 = c * v 1)).card =
    q ^ 2 := by
    intro c
    rw [show q ^ 2 = q * q from by ring, ← Fintype.card_prod, ← Fintype.card_subtype]
    apply Fintype.card_congr
    exact Equiv.ofBijective (fun ⟨v, hv⟩ => (v 1, v 2)) ⟨
      fun ⟨v, hv⟩ ⟨w, hw⟩ h => by
        simp only [Prod.mk.injEq] at h
        exact Subtype.ext (funext fun i => by fin_cases i <;> simp_all),
      fun ⟨y, z⟩ => ⟨⟨![c * y, y, z], by simp [Matrix.cons_val_zero]⟩,
        by simp [Matrix.cons_val_one]⟩⟩
  have hL1 : L1.card = q ^ 2 := hline d
  have hL2 : L2.card = q ^ 2 := by convert hline (-d) using 2; ext v; simp [L2, neg_mul]
  have hinter : (L1 ∩ L2).card = q := by
    rw [← filter_and, ← Fintype.card_subtype]
    apply Fintype.card_congr
    refine Equiv.ofBijective (fun ⟨v, hv1, hv2⟩ => v 2) ⟨?_, ?_⟩
    · intro ⟨v, hv1, hv2⟩ ⟨w, hw1, hw2⟩ heq
      simp only at heq
      have get_zero : ∀ {u : Fin 3 → K}, u 0 = d * u 1 → u 0 = -(d * u 1) → u 1 = 0 := by
        intro u hu1 hu2
        have h : d * u 1 = -(d * u 1) := hu1 ▸ hu2
        have h2 : 2 * (d * u 1) = 0 := by
          have := sub_eq_zero.mpr h; linear_combination this
        rw [show 2 * (d * u 1) = (2 * d) * u 1 from by ring] at h2
        exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero h2K hd)
      have hv1_0 := get_zero hv1 hv2
      have hv0_0 : v 0 = 0 := by rw [hv1, hv1_0, mul_zero]
      have hw1_0 := get_zero hw1 hw2
      have hw0_0 : w 0 = 0 := by rw [hw1, hw1_0, mul_zero]
      exact Subtype.ext (funext fun i => by fin_cases i <;> simp_all)
    · intro z
      exact ⟨⟨![0, 0, z], by constructor <;> simp⟩, by simp⟩
  have hie := card_union_add_card_inter L1 L2
  rw [hL1, hL2, hinter] at hie; omega

/--
[geom_irred_conic_has_q_plus_one_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma geom_irred_conic_has_q_plus_one_points
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {a b c : K}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0) :
-- imply
  projConicCount K a b c = Fintype.card K + 1 := by
-- proof
  unfold projConicCount
  rw [affineSolCount_irred K a b c ha hb hc]
  set q := Fintype.card K
  have hq : q ≥ 2 := Fintype.one_lt_card (α := K)
  have hq1 : 0 < q - 1 := by omega
  have hle : 1 ≤ q ^ 2 := by nlinarith
  have key : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [hle, show 1 ≤ q from by omega]
    ring
  rw [key, Nat.mul_div_cancel _ hq1]

/--
[double_line_conic_has_q_plus_one_points_char2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma double_line_conic_has_q_plus_one_points_char2
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  [CharP K 2]
  {a b : K}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  projConicCount K a b 0 = Fintype.card K + 1 := by
-- proof
  unfold projConicCount
  rw [affineSolCount_double_line_char2 K a b ha hb]
  set q := Fintype.card K
  have hq : q ≥ 2 := Fintype.one_lt_card (α := K)
  have hq1 : 0 < q - 1 := by omega
  have hle : 1 ≤ q ^ 2 := by nlinarith
  have key : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [hle, show 1 ≤ q from by omega]
    ring
  rw [key, Nat.mul_div_cancel _ hq1]

/--
[split_base_conic_has_2q_plus_one_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma split_base_conic_has_2q_plus_one_points
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {a b : K}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hsq : IsSquare (-b * a⁻¹))
  (hchar : ringChar K ≠ 2) :
-- imply
  projConicCount K a b 0 = 2 * Fintype.card K + 1 := by
-- proof
  unfold projConicCount
  rw [affineSolCount_split_base K a b ha hb hsq hchar]
  set q := Fintype.card K
  have hq : q ≥ 2 := Fintype.one_lt_card (α := K)
  have hq1 : 0 < q - 1 := by omega
  have hle : q ≤ 2 * q ^ 2 := by nlinarith
  have hle2 : 1 ≤ 2 * q ^ 2 - q := by zify [hle]; nlinarith
  have key : 2 * q ^ 2 - q - 1 = (2 * q + 1) * (q - 1) := by
    zify [hle, hle2, show 1 ≤ q from by omega]
    ring
  rw [key, Nat.mul_div_cancel _ hq1]

/--
[split_ext_conic_has_one_point](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma split_ext_conic_has_one_point
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {a b : K}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hnsq : ¬IsSquare (-b * a⁻¹)) :
-- imply
  projConicCount K a b 0 = 1 := by
-- proof
  unfold projConicCount affineSolCount
  have hbij : Fintype.card { v : Fin 3 → K // a * (v 0) ^ 2 + b * (v 1) ^ 2 + 0 * (v 2) ^ 2 = 0 } =
    Fintype.card K := by
    apply Fintype.card_congr
    refine Equiv.ofBijective (fun ⟨v, hv⟩ => v 2) ⟨?_, ?_⟩
    · intro ⟨v, hv⟩ ⟨w, hw⟩ h
      simp only at h
      have hv_eq : a * (v 0) ^ 2 + b * (v 1) ^ 2 = 0 := by linear_combination hv
      have hw_eq : a * (w 0) ^ 2 + b * (w 1) ^ 2 = 0 := by linear_combination hw
      have ⟨hv0, hv1⟩ := diag_binary_form_trivial_of_not_square a b ha hb hnsq hv_eq
      have ⟨hw0, hw1⟩ := diag_binary_form_trivial_of_not_square a b ha hb hnsq hw_eq
      exact Subtype.ext (funext fun i => by fin_cases i <;> simp_all)
    · intro z
      exact ⟨⟨![0, 0, z], by simp⟩, by simp⟩
  rw [hbij]
  exact Nat.div_self (by have := Fintype.one_lt_card (α := K); omega)

/--
[conic_projective_point_count_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma conic_projective_point_count_trichotomy
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {a b c : K}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hchar : ringChar K ≠ 2) :
-- imply
  (DiagConicIsGeomIrreducible a b c ∧ projConicCount K a b c = Fintype.card K + 1) ∨ (DiagConicIsSplitOverBase a b c ∧ projConicCount K a b c = 2 * Fintype.card K + 1) ∨ (DiagConicIsSplitOverExtension a b c ∧ projConicCount K a b c = 1) := by
-- proof
  by_cases hc : c = 0
  · subst hc
    by_cases hsq : IsSquare (-b * a⁻¹)
    · exact Or.inr (Or.inl ⟨⟨rfl, hsq⟩, split_base_conic_has_2q_plus_one_points K a b ha hb hsq hchar⟩)
    · exact Or.inr (Or.inr ⟨⟨rfl, hsq⟩, split_ext_conic_has_one_point K a b ha hb hsq⟩)
  · exact Or.inl ⟨hc, geom_irred_conic_has_q_plus_one_points K a b c ha hb hc⟩

/--
[conic_projective_point_count_trichotomy_all_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma conic_projective_point_count_trichotomy_all_char
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {a b c : K}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  projConicCount K a b c = Fintype.card K + 1 ∨ projConicCount K a b c = 2 * Fintype.card K + 1 ∨ projConicCount K a b c = 1 := by
-- proof
  by_cases hc : c = 0
  · subst hc
    obtain h2 | hodd := eq_or_ne (ringChar K) 2
    ·
      haveI : CharP K 2 := by rw [← h2]; exact ringChar.charP K
      exact Or.inl (double_line_conic_has_q_plus_one_points_char2 K a b ha hb)
    ·
      by_cases hsq : IsSquare (-b * a⁻¹)
      · exact Or.inr (Or.inl (split_base_conic_has_2q_plus_one_points K a b ha hb hsq hodd))
      · exact Or.inr (Or.inr (split_ext_conic_has_one_point K a b ha hb hsq))
  · exact Or.inl (geom_irred_conic_has_q_plus_one_points K a b c ha hb hc)

/--
[conic_point_count_cong_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma conic_point_count_cong_one
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {a b c : K}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  projConicCount K a b c ≡ 1 [MOD Fintype.card K] := by
-- proof
  set q := Fintype.card K
  obtain h | h | h := conic_projective_point_count_trichotomy_all_char K a b c ha hb
  ·
    rw [h, Nat.ModEq.comm]
    exact (Nat.modEq_iff_dvd' (by omega)).mpr (dvd_refl q)
  ·
    rw [h, Nat.ModEq.comm]
    exact (Nat.modEq_iff_dvd' (by omega)).mpr ⟨2, by omega⟩
  ·
    rw [h]

/--
[q_dvd_projConicCount_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean)
-/
@[path]
lemma q_dvd_projConicCount_sub_one
  {K : Type*}
  [Field K]
  [Fintype K]
  [DecidableEq K]
  {a b c : K}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  Fintype.card K ∣ projConicCount K a b c - 1 := by
-- proof
  have h_le : 1 ≤ projConicCount K a b c := by
    obtain h | h | h <;> omega := conic_projective_point_count_trichotomy_all_char K a b c ha hb
  exact (Nat.modEq_iff_dvd' h_le).mp
    (conic_point_count_cong_one K a b c ha hb).symm


-- created on 2026-10-23
