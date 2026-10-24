import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728.lean)
-/
@[path]
private lemma main
  [Field k] {q : ℕ} [Fact q.Prime] [CharP k q] (hq : 5 ≤ q)
  (a : k) (h01728 : a = 0 ∨ a = 1728) (l : k)
  (hl : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3) :
  -- imply
  l ^ (q ^ 2) = l := by
  -- proof
  have hp : q.Prime := Fact.out
  have hqodd : Odd q := hp.odd_of_ne_two (by omega)
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : k) = 0 := by
      exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k q] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h3 : (3 : k) ≠ 0 := by
    intro h
    have : ((3 : ℕ) : k) = 0 := by
      exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k q] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h16 : (16 : k) ≠ 0 := by
    have : (16 : k) = 2 ^ 4 := by
      norm_num
    rw [this]
    refine pow_ne_zero _ h2
  have hfrobC : ∀ n : ℕ, ((OfNat.ofNat n.succ.succ : k)) ^ q = OfNat.ofNat n.succ.succ := by
    intro n
    have this := map_ofNat (frobenius k q) n.succ.succ
    rw [frobenius_def] at this
    refine this
  have h16q : (16 : k) ^ q = 16 := hfrobC 14
  have h16qq : (16 : k) ^ (q ^ 2) = 16 := by
    rw [pow_two, pow_mul, h16q, h16q]
  set lam : k := 16 * l with hlam
  have hlamqq : lam ^ (q ^ 2) = lam := by
    cases h01728
    ·
      rename_i ha
      subst ha
      have h256 : (256 : k) ≠ 0 := by
        have : (256 : k) = 2 ^ 8 := by
          norm_num
        rw [this]
        refine pow_ne_zero _ h2
      have hP : lam ^ 2 - lam + 1 = 0 := by
        rw [zero_mul] at hl
        have := (mul_eq_zero.mp hl.symm).resolve_left h256
        refine pow_eq_zero_iff (by norm_num) |>.mp this
      have h3' : lam ^ 3 = -1 := by
        linear_combination (lam + 1) * hP
      have h6 : lam ^ 6 = 1 := by
        have : lam ^ 6 = (lam ^ 3) ^ 2 := by
          ring
        rw [this, h3']
        ring
      have hmod : q ^ 2 % 6 = 1 := by
        have h2n : ¬ 2 ∣ q := fun h => by
          cases hp.eq_one_or_self_of_dvd 2 h
          ·
            rename_i hdiv
            omega
          ·
            rename_i hdiv
            omega
        have h3n : ¬ 3 ∣ q := fun h => by
          cases hp.eq_one_or_self_of_dvd 3 h
          ·
            rename_i hdiv
            omega
          ·
            rename_i hdiv
            omega
        have : q % 6 = 1 ∨ q % 6 = 5 := by
          omega
        rw [Nat.pow_mod]
        cases this
        ·
          rename_i hmod
          simp [hmod]
        ·
          rename_i hmod
          simp [hmod]
      have hdecomp : q ^ 2 = 6 * (q ^ 2 / 6) + 1 := by
        have := Nat.div_add_mod (q ^ 2) 6
        omega
      rw [hdecomp, pow_add, pow_mul, h6, one_pow, one_mul, pow_one]
    ·
      rename_i ha
      subst ha
      have hfac : (64 : k) * ((lam + 1) ^ 2 * (lam - 2) ^ 2 * (2 * lam - 1) ^ 2) = 0 := by
        linear_combination (-1 : k) * hl
      have h64 : (64 : k) ≠ 0 := by
        have : (64 : k) = 2 ^ 6 := by
          norm_num
        rw [this]
        refine pow_ne_zero _ h2
      have hprod := (mul_eq_zero.mp hfac).resolve_left h64
      have hlamq : lam ^ q = lam := by
        cases mul_eq_zero.mp hprod
        ·
          rename_i h
          cases mul_eq_zero.mp h
          ·
            rename_i hsq
            have : lam = -1 := by
              have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
              linear_combination this
            rw [this, hqodd.neg_one_pow]
          ·
            rename_i hsq
            have : lam = 2 := by
              have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
              linear_combination this
            rw [this]
            refine hfrobC 0
        ·
          rename_i h
          have : lam = 2⁻¹ := by
            have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
            field_simp
            linear_combination h'
          rw [this, inv_pow, hfrobC 0]
      rw [pow_two, pow_mul, hlamq, hlamq]
  have hl16 : l = lam / 16 := by
    rw [hlam]
    field_simp
  rw [hl16, div_pow, hlamqq, h16qq]


-- created on 2026-10-20
