import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma eq_one_of_pow_prime_eq_one {A : Type} [CommRing A] [IsDomain A] {n : Type} [Fintype n] [DecidableEq n] (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) (ℓ : ℕ) (hℓ𝔪 : (ℓ : A) ∉ 𝔪) (M : Matrix n n A) (hM : ∀ i j : n, M i j - (1 : Matrix n n A) i j ∈ 𝔪) (hpow : M ^ ℓ = 1) : M = 1 := by
  classical
  let _ : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let φ : Matrix n n A →+* Matrix n n (A ⧸ 𝔪) := (Ideal.Quotient.mk 𝔪).mapMatrix
  have hφM : φ M = 1 := by
    ext i j
    rw [Matrix.map_apply]
    simpa [Matrix.one_apply, apply_ite (Ideal.Quotient.mk 𝔪), map_one, map_zero] using ((Ideal.Quotient.eq (I := 𝔪)).2 (hM i j))
  set u : Matrix n n A := ∑ k ∈ Finset.range ℓ, M ^ k with hu
  have hu0 : u * (M - 1) = 0 := by
    rw [hu, geom_sum_mul, hpow, sub_self]
  have hφu : φ u = (ℓ : A ⧸ 𝔪) • (1 : Matrix n n (A ⧸ 𝔪)) := by
    rw [hu, map_sum]
    simp only [map_pow, hφM, one_pow, Finset.sum_const, Finset.card_range]
    apply (Nat.cast_smul_eq_nsmul (A ⧸ 𝔪) ℓ (1 : Matrix n n (A ⧸ 𝔪))).symm
  have hdetφ : (φ u).det ≠ 0 := by
    rw [hφu, Matrix.det_smul, Matrix.det_one, mul_one]
    apply pow_ne_zero _ (mt (Ideal.Quotient.eq_zero_iff_mem).1 hℓ𝔪)
  have hdet : u.det ≠ 0 := by
    intro h0
    apply hdetφ
    rw [show φ u = (Ideal.Quotient.mk 𝔪).mapMatrix u from rfl, ← RingHom.map_det, h0, map_zero]
  have h2 : u.det • (M - 1) = 0 := calc
    _ = (u.det • (1 : Matrix n n A)) * (M - 1) := by
      rw [smul_mul_assoc, one_mul]
    _ = u.adjugate * u * (M - 1) := by
      rw [Matrix.adjugate_mul]
    _ = 0 := by
      rw [Matrix.mul_assoc, hu0, Matrix.mul_zero]
  rw [← sub_eq_zero]
  ext i j
  have h := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, mul_eq_zero] at h
  obtain h | h := h
  ·
    apply absurd h hdet
  ·
    apply h
/--
[Matrix_GeneralLinearGroup_eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_GeneralLinearGroup_eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne.lean)
-/
@[path]
private lemma main
  (A : Type) [CommRing A] [IsDomain A] [CharZero A]
  (𝔪₁ 𝔪₂ : Ideal A) (h𝔪₁ : 𝔪₁.IsMaximal) (h𝔪₂ : 𝔪₂.IsMaximal)
  (p₁ p₂ : ℕ) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) (hp₁𝔪 : (p₁ : A) ∈ 𝔪₁) (hp₂𝔪 : (p₂ : A) ∈ 𝔪₂)
  (n : Type) [Fintype n] [DecidableEq n]
  (g : Matrix.GeneralLinearGroup n A) (hg : IsOfFinOrder g)
  (hg₁ : ∀ i j : n, (g : Matrix n n A) i j - (1 : Matrix n n A) i j ∈ 𝔪₁)
  (hg₂ : ∀ i j : n, (g : Matrix n n A) i j - (1 : Matrix n n A) i j ∈ 𝔪₂) :
  -- imply
  g = 1 := by
  -- proof
  classical
  by_contra hg1
  set m := orderOf g with hm
  have hmpos : 0 < m := hg.orderOf_pos
  have hm1 : m ≠ 1 := by
    rw [hm]
    apply mt orderOf_eq_one_iff.1 hg1
  let ℓ := m.minFac
  have hℓ : ℓ.Prime := Nat.minFac_prime hm1
  have hℓm : ℓ ∣ m := Nat.minFac_dvd m
  set g' : Matrix.GeneralLinearGroup n A := g ^ (m / ℓ) with hg'
  have hg'pow : g' ^ ℓ = 1 := by
    rw [hg', ← pow_mul, Nat.div_mul_cancel hℓm, hm, pow_orderOf_eq_one]
  have hg'ne : g' ≠ 1 := by
    rw [hg']
    apply pow_ne_one_of_lt_orderOf (Nat.div_pos (Nat.le_of_dvd hmpos hℓm) hℓ.pos).ne'
    rw [← hm]
    apply Nat.div_lt_self hmpos hℓ.one_lt
  have cong : ∀ (𝔪 : Ideal A), (∀ i j : n, (g : Matrix n n A) i j - (1 : Matrix n n A) i j ∈ 𝔪) → ∀ i j : n, (g' : Matrix n n A) i j - (1 : Matrix n n A) i j ∈ 𝔪 := by
    intro 𝔪 h i j
    let φ : Matrix n n A →+* Matrix n n (A ⧸ 𝔪) := (Ideal.Quotient.mk 𝔪).mapMatrix
    have hφ : φ (g : Matrix n n A) = 1 := by
      ext i j
      rw [Matrix.map_apply]
      simpa [Matrix.one_apply, apply_ite (Ideal.Quotient.mk 𝔪), map_one, map_zero] using ((Ideal.Quotient.eq (I := 𝔪)).2 (h i j))
    have hφ' : φ (g' : Matrix n n A) = 1 := by
      rw [hg', Units.val_pow_eq_pow_val, map_pow, hφ, one_pow]
    have h := congrFun (congrFun hφ' i) j
    apply (Ideal.Quotient.eq (I := 𝔪)).1
    rw [Matrix.map_apply] at h
    simpa [Matrix.one_apply, apply_ite (Ideal.Quotient.mk 𝔪), map_one, map_zero] using h
  have key : ∀ (𝔪 : Ideal A) (p : ℕ), 𝔪.IsMaximal → p.Prime → (p : A) ∈ 𝔪 → (ℓ : A) ∈ 𝔪 → ℓ = p := by
    intro 𝔪 p hmax hp hp𝔪 hℓ𝔪
    by_contra hne'
    have hcop : IsCoprime (ℓ : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hℓ hp).2 hne')
    obtain ⟨a, b, hab⟩ := hcop
    have : (1 : A) ∈ 𝔪 := by
      have e : ((a : ℤ) : A) * (ℓ : A) + ((b : ℤ) : A) * (p : A) = 1 := by
        exact_mod_cast congrArg (Int.cast : ℤ → A) hab
      rw [← e]
      apply 𝔪.add_mem (𝔪.mul_mem_left _ hℓ𝔪) (𝔪.mul_mem_left _ hp𝔪)
    apply hmax.ne_top ((Ideal.eq_top_iff_one 𝔪).2 this)
  have hor : (ℓ : A) ∉ 𝔪₁ ∨ (ℓ : A) ∉ 𝔪₂ := by
    by_contra hh
    push Not at hh
    apply hne ((key 𝔪₁ p₁ h𝔪₁ hp₁ hp₁𝔪 hh.1).symm.trans (key 𝔪₂ p₂ h𝔪₂ hp₂ hp₂𝔪 hh.2))
  have hval : (g' : Matrix n n A) ^ ℓ = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg'pow, Units.val_one]
  apply hg'ne
  apply Units.ext
  obtain h | h := hor
  ·
    apply eq_one_of_pow_prime_eq_one 𝔪₁ h𝔪₁ ℓ h _ (cong 𝔪₁ hg₁) hval
  ·
    apply eq_one_of_pow_prime_eq_one 𝔪₂ h𝔪₂ ℓ h _ (cong 𝔪₂ hg₂) hval


-- created on 2026-10-20
