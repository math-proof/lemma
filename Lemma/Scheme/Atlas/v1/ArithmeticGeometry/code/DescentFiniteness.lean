import Mathlib
import sympy.Basic
import Structure.v1.Atlas.ArithmeticGeometry.code.DescentFiniteness
open Int in


/--
[squarefree_dvd_B_of_descent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/DescentFiniteness.lean)
-/
@[path]
lemma squarefree_dvd_B_of_descent
  {A B r ℓ m σ : ℤ}
-- given
  (hr_sq : Squarefree r)
  (hcop : IsCoprime ℓ m)
  (heq : r ^ 2 * ℓ ^ 4 + A * r * ℓ ^ 2 * m ^ 2 + B * m ^ 4 = r * m ^ 4 * σ ^ 2) :
-- imply
  r ∣ B := by
-- proof
  have h_r_dvd_Bm4 : r ∣ B * m ^ 4 :=
    ⟨m ^ 4 * σ ^ 2 - (r * ℓ ^ 4 + A * ℓ ^ 2 * m ^ 2), by linarith⟩
  suffices hcop_rm : IsCoprime r m by
    exact (hcop_rm.pow_right (n := 4)).dvd_of_dvd_mul_left (by rwa [mul_comm] at h_r_dvd_Bm4)
  by_contra h_not_cop
  rw [Int.isCoprime_iff_gcd_eq_one] at h_not_cop
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd h_not_cop
  have hpr : (p : ℤ) ∣ r := dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_left r m)
  have hpm : (p : ℤ) ∣ m := dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_right r m)
  have h_p3_dvd : (p : ℤ) ^ 3 ∣ r ^ 2 * ℓ ^ 4 := by
    obtain ⟨r', hr'⟩ := hpr; obtain ⟨m', hm'⟩ := hpm
    have heq' : r ^ 2 * ℓ ^ 4 =
      r * m ^ 4 * σ ^ 2 - A * r * ℓ ^ 2 * m ^ 2 - B * m ^ 4 := by linarith
    rw [heq']
    have h1 : A * r * ℓ ^ 2 * m ^ 2 = (p : ℤ) ^ 3 * (A * r' * ℓ ^ 2 * m' ^ 2) := by
      subst hr'; subst hm'; ring
    have h2 : B * m ^ 4 = (p : ℤ) ^ 3 * ((p : ℤ) * B * m' ^ 4) := by
      subst hm'; ring
    have h3 : r * m ^ 4 * σ ^ 2 =
      (p : ℤ) ^ 3 * ((p : ℤ) ^ 2 * r' * m' ^ 4 * σ ^ 2) := by
      subst hr'; subst hm'; ring
    rw [h1, h2, h3]
    exact ⟨(p : ℤ) ^ 2 * r' * m' ^ 4 * σ ^ 2 - A * r' * ℓ ^ 2 * m' ^ 2 -
      (p : ℤ) * B * m' ^ 4, by ring⟩
  have hp_dvd_ℓ : (p : ℤ) ∣ ℓ := by
    obtain ⟨k, hk⟩ := hpr
    have hpk : ¬ ((p : ℤ) ∣ k) := by
      intro ⟨j, hj⟩
      have hu := hr_sq _ ⟨j, by rw [hk, hj]; ring⟩
      rw [Int.isUnit_iff] at hu
      obtain hu | hu := hu
      · exact hp.one_lt.ne' (by exact_mod_cast hu)
      · have := Int.natCast_nonneg p; omega
    have h' : (p : ℤ) ∣ k ^ 2 * ℓ ^ 4 := by
      rw [show r ^ 2 * ℓ ^ 4 = (p : ℤ) ^ 2 * (k ^ 2 * ℓ ^ 4) from by rw [hk]; ring]
        at h_p3_dvd
      exact (mul_dvd_mul_iff_left
        (pow_ne_zero 2 (Int.natCast_ne_zero.mpr hp.ne_zero))).mp h_p3_dvd
    have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact hp_int.dvd_of_dvd_pow
      ((hp_int.dvd_or_dvd h').resolve_left (fun h => hpk (hp_int.dvd_of_dvd_pow h)))
  exact (Nat.prime_iff_prime_int.mp hp).not_unit (hcop.isUnit_of_dvd' hp_dvd_ℓ hpm)

/--
[lemma_25_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/DescentFiniteness.lean)
-/
@[path]
lemma lemma_25_5
  {A B : ℤ}
-- given
  (hB : B ≠ 0) :
-- imply
  Set.Finite {r : ℤ | Squarefree r ∧ ∃ ℓ m σ : ℤ, IsCoprime ℓ m ∧ r ^ 2 * ℓ ^ 4 + A * r * ℓ ^ 2 * m ^ 2 + B * m ^ 4 = r * m ^ 4 * σ ^ 2} := by
-- proof
  apply Set.Finite.subset (Set.Finite.subset (Set.finite_Icc (-|B|) |B|) _)
  ·
    intro r ⟨hr_sq, ℓ, m, σ, hcop, heq⟩
    exact squarefree_dvd_B_of_descent A B r ℓ m σ hr_sq hcop heq
  ·
    intro r hr
    simp only [Set.mem_Icc]
    have hBpos : 0 < |B| := abs_pos.mpr hB
    exact ⟨by linarith [neg_abs_le r, Int.le_of_dvd hBpos ((abs_dvd_abs r B).2 hr)],
      by linarith [le_abs_self r, Int.le_of_dvd hBpos ((abs_dvd_abs r B).2 hr)]⟩

/--
[lemma_25_5_image_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/DescentFiniteness.lean)
-/
@[path]
lemma lemma_25_5_image_finite
  {E'Q : Type}
  [AddCommGroup E'Q]
  {π : E'Q →+ Additive (ℚˣ ⧸ Subgroup.square ℚˣ)}
  {B : ℤ}
  {intRepr : ℚˣ ⧸ Subgroup.square ℚˣ → ℤ}
-- given
  (hB : B ≠ 0)
  (hRepr_inj : Function.Injective intRepr)
  (hπ_dvd : ∀ P : E'Q, intRepr (Additive.toMul (π P)) ∣ B) :
-- imply
  Set.Finite (Set.range π) := by
-- proof
  have h_fin_divs : Set.Finite {r : ℤ | r ∣ B} := by
    apply Set.Finite.subset (Set.finite_Icc (-|B|) |B|)
    intro r hr
    simp only [Set.mem_Icc]
    have hBpos : 0 < |B| := abs_pos.mpr hB
    exact ⟨by linarith [neg_abs_le r, Int.le_of_dvd hBpos ((abs_dvd_abs r B).2 hr)],
      by linarith [le_abs_self r, Int.le_of_dvd hBpos ((abs_dvd_abs r B).2 hr)]⟩
  let f : Additive (ℚˣ ⧸ Subgroup.square ℚˣ) → ℤ := intRepr ∘ Additive.toMul
  have hf_inj : Function.Injective f := hRepr_inj.comp Additive.toMul.injective
  have hf_image_sub : f '' Set.range π ⊆ {r : ℤ | r ∣ B} := by
    rintro r ⟨x, ⟨P, rfl⟩, rfl⟩
    exact hπ_dvd P
  exact (h_fin_divs.subset hf_image_sub).of_finite_image hf_inj.injOn


-- created on 2026-10-23
