/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/Period.lean -/


import Def.NumberTheory.DirichletCharacter.Period
import Lemma.Nat.DirichletCharacter.Period
import Mathlib.Data.Complex.Basic
open MonoidHom

/-!
# Tests for Dirichlet character periods (ATLAS `NumberTheoryI` Lemma 18.8)
-/


/-- Regression: the constant-one map has least period `1`. -/
example : Function.Periodic (1 : ℤ →* ℂ) ((1 : ℕ) : ℤ) ∧
    ∀ d : ℕ, 0 < d → Function.Periodic (1 : ℤ →* ℂ) (d : ℤ) → 1 ≤ d :=
  ⟨one_period, one_map_min⟩

/-- Regression: the constant-one map is a modulus-`1` character, proved directly
from the definition, so modulus `1` is nonvacuous. -/
example : (1 : ℤ →* ℂ).IsDirichletCharacterModulus 1 := by
  have h1 : ∀ x : ℤ, (1 : ℤ →* ℂ) x = 1 := by simp
  refine ⟨fun x => by simp [h1], fun n => ?_⟩
  rw [h1 n]
  exact iff_of_true one_ne_zero isCoprime_one_left

/-- The iff API builds the modulus-`1` character from its period data. -/
example : (1 : ℤ →* ℂ).IsDirichletCharacterModulus 1 := by
  rw [isDirichletCharacterModulus_iff (by norm_num) one_period one_map_min
    (by norm_num)]
  exact ⟨dvd_rfl, 0, by simp⟩

/-- Regression: the constant-one map is not a modulus-`2` character. -/
example : ¬ (1 : ℤ →* ℂ).IsDirichletCharacterModulus 2 := by
  intro h
  rw [isDirichletCharacterModulus_iff (by norm_num) one_period one_map_min
    (by norm_num)] at h
  obtain ⟨-, k, hk⟩ := h
  rw [one_pow] at hk
  exact (by decide : ¬ 2 ∣ 1) hk

/-- The corollary: the constant-one map has modulus `1 = m`. -/
example : (1 : ℤ →* ℂ).IsDirichletCharacterModulus 1 :=
  isDirichletCharacterModulus_self (by norm_num) one_period one_map_min

/-- Forward use of the iff: a modulus hypothesis yields `m ∣ m'`. -/
example {R : Type*} [MonoidWithZero R] [Nontrivial R] [IsCancelMulZero R]
    {χ : ℤ →* R} {m m' : ℕ} (hm : 0 < m)
    (hper : Function.Periodic χ (m : ℤ))
    (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d)
    (hm' : 0 < m') (h : χ.IsDirichletCharacterModulus m') : m ∣ m' :=
  ((isDirichletCharacterModulus_iff hm hper hmin hm').mp h).1

/-- `m * p` is excluded as a modulus when `p` is prime and `p ∤ m`. -/
example {R : Type*} [MonoidWithZero R] [Nontrivial R] [IsCancelMulZero R]
    {χ : ℤ →* R} {m p : ℕ} (hm : 0 < m)
    (hper : Function.Periodic χ (m : ℤ))
    (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d)
    (hp : Nat.Prime p) (hdiv : ¬ p ∣ m) :
    ¬ χ.IsDirichletCharacterModulus (m * p) := by
  intro h
  have hm' : 0 < m * p := Nat.mul_pos hm hp.pos
  rw [isDirichletCharacterModulus_iff hm hper hmin hm'] at h
  obtain ⟨-, k, hk⟩ := h
  exact hdiv (hp.dvd_of_dvd_pow (dvd_trans (dvd_mul_left p m) hk))

/-- Positive powers `m ^ r` are moduli. -/
example {R : Type*} [MonoidWithZero R] [Nontrivial R] [IsCancelMulZero R]
    {χ : ℤ →* R} {m r : ℕ} (hm : 0 < m)
    (hper : Function.Periodic χ (m : ℤ))
    (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d)
    (hr : 0 < r) : χ.IsDirichletCharacterModulus (m ^ r) := by
  have hm' : 0 < m ^ r := pow_pos hm r
  rw [isDirichletCharacterModulus_iff hm hper hmin hm']
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (ne_of_gt hr)
  exact ⟨dvd_pow_self m (by omega), s + 1, dvd_rfl⟩

