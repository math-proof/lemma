import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.DirichletCharacter.Period
open MonoidHom


namespace MonoidHom

variable [MonoidWithZero R]
/--
[chi_neg_one_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
private lemma chi_neg_one_ne_zero {χ : ℤ →* R} [Nontrivial R] :
  χ (-1) ≠ 0 := by
  have hsq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, show (-1 : ℤ) * -1 = 1 by norm_num, map_one]
  intro hz
  rw [hz, zero_mul] at hsq
  exact one_ne_zero hsq.symm

end MonoidHom

namespace MonoidHom

variable [MonoidWithZero R]
/--
[chi_natAbs_ne_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
private lemma chi_natAbs_ne_zero_iff {χ : ℤ →* R} [Nontrivial R]
  [IsCancelMulZero R] (n : ℤ) :
  χ n ≠ 0 ↔ χ ((n.natAbs : ℕ) : ℤ) ≠ 0 := by
  set N : ℕ := n.natAbs with hN
  obtain h | h := Int.natAbs_eq n
  · rw [h]
  · have hmap : χ (-((N : ℕ) : ℤ)) = χ (-1) * χ ((N : ℕ) : ℤ) := by
    rw [show (-((N : ℕ) : ℤ)) = (-1) * ((N : ℕ) : ℤ) by ring, map_mul]
    rw [h, hmap]
    exact ⟨fun hne h0 => hne (by rw [h0, mul_zero]),
      fun hne => mul_ne_zero chi_neg_one_ne_zero hne⟩

end MonoidHom

namespace MonoidHom

variable [MonoidWithZero R]
/--
[isCoprime_natAbs_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
private lemma isCoprime_natAbs_iff (m : ℕ) (n : ℤ) :
  IsCoprime (m : ℤ) n ↔ Nat.Coprime m n.natAbs := by
  rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]

end MonoidHom

namespace MonoidHom

variable [MonoidWithZero R]
/--
[period_dvd_of_min](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
`d % m` inherits periodicity, so minimality forces it to vanish). -/
private lemma period_dvd_of_min {χ : ℤ →* R} {m : ℕ} (hm : 0 < m)
  (hper : Function.Periodic χ (m : ℤ))
  (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d)
  {d : ℕ} (hdper : Function.Periodic χ (d : ℤ)) : m ∣ d := by
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra hne
  have hmod : 0 < d % m := Nat.pos_of_ne_zero hne
  have hper_mod : Function.Periodic χ ((d % m : ℕ) : ℤ) := by
    have hsub := hdper.sub_period (hper.nsmul (d / m))
    have heq : ((d % m : ℕ) : ℤ) = (d : ℤ) - (d / m) • (m : ℤ) := by
      have hdm := Nat.div_add_mod d m
      have hcast : ((m * (d / m) + d % m : ℕ) : ℤ) = (d : ℤ) := by
        exact_mod_cast hdm
      rw [Nat.cast_add, Nat.cast_mul] at hcast
      rw [nsmul_eq_mul, mul_comm ((d / m : ℕ) : ℤ) (m : ℤ)]
      omega
    rwa [heq]
  have hle := hmin _ hmod hper_mod
  have hlt := Nat.mod_lt d hm
  omega

end MonoidHom

namespace MonoidHom

variable [MonoidWithZero R]
/--
[periodic_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
private lemma periodic_of_dvd {χ : ℤ →* R} {m m' : ℕ}
  (hper : Function.Periodic χ (m : ℤ)) (h : m ∣ m') :
  Function.Periodic χ ((m' : ℕ) : ℤ) := by
  obtain ⟨t, rfl⟩ := h
  have hcast : ((m * t : ℕ) : ℤ) = (t : ℕ) * (m : ℤ) := by
    rw [Nat.cast_mul, mul_comm]
  rw [hcast]
  exact hper.nat_mul t

end MonoidHom

namespace MonoidHom

variable [MonoidWithZero R]
/--
[periodic_eq_of_add_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
private lemma periodic_eq_of_add_mul {χ : ℤ →* R} {m : ℕ}
  (hper : Function.Periodic χ (m : ℤ)) (a t : ℤ) :
  χ (a + (m : ℤ) * t) = χ a := by
  have h := hper.zsmul t a
  rwa [Int.zsmul_eq_mul, mul_comm t] at h

end MonoidHom

namespace MonoidHom

variable [MonoidWithZero R]
/--
[periodic_eq_of_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
private lemma periodic_eq_of_modEq {χ : ℤ →* R} {m : ℕ}
  (hper : Function.Periodic χ (m : ℤ)) {a b : ℤ}
  (h : a ≡ b [ZMOD (m : ℤ)]) : χ a = χ b := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp h
  have hba : b = a + (m : ℤ) * t := by rw [← ht]; ring
  rw [hba]
  exact (periodic_eq_of_add_mul hper a t).symm

end MonoidHom

namespace MonoidHom

variable [MonoidWithZero R]
/--
[nonzero_imp_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
would give `χ p ≠ 0` (else `χ n = 0`) while `m / p` is a smaller period
(cancelling the nonzero `χ p`). -/
private lemma nonzero_imp_coprime {χ : ℤ →* R} [IsCancelMulZero R] {m : ℕ}
  (hm : 0 < m)
  (hper : Function.Periodic χ (m : ℤ))
  (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d)
  {n : ℤ} (hn : χ n ≠ 0) : IsCoprime (m : ℤ) n := by
  rw [isCoprime_natAbs_iff]
  by_contra hnc
  obtain ⟨p, hpprime, hpm, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  have hpdvd : (p : ℤ) ∣ n := Int.natCast_dvd.mpr hpn
  have hχp : χ (p : ℤ) ≠ 0 := by
    intro h0
    obtain ⟨t, ht⟩ := hpdvd
    exact hn (by rw [ht, map_mul, h0, zero_mul])
  have hdivpos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hpm) hpprime.pos
  have hdivlt : m / p < m := Nat.div_lt_self hm hpprime.one_lt
  have hperdiv : Function.Periodic χ ((m / p : ℕ) : ℤ) := by
    intro r
    have hper_r := hper (r * (p : ℤ))
    have hdecomp : r * (p : ℤ) + (m : ℤ) = (r + ((m / p : ℕ) : ℤ)) * (p : ℤ) := by
      have hcancel := Nat.div_mul_cancel hpm
      have hcast : (((m / p * p : ℕ)) : ℤ) = (m : ℤ) := by exact_mod_cast hcancel
      rw [Nat.cast_mul] at hcast
      rw [hcast.symm]
      ring
    simp only [map_mul] at hper_r
    rw [hdecomp] at hper_r
    simp only [map_mul] at hper_r
    exact mul_right_cancel₀ hχp hper_r
  have hle := hmin _ hdivpos hperdiv
  omega

end MonoidHom

namespace MonoidHom

variable [MonoidWithZero R]
/--
[coprime_imp_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
`N ^ φ ≡ 1 [MOD m]`, so `χ N ^ φ = χ 1 = 1`. -/
private lemma coprime_imp_nonzero {χ : ℤ →* R} [Nontrivial R]
  [IsCancelMulZero R] {m : ℕ} (hm : 0 < m)
  (hper : Function.Periodic χ (m : ℤ))
  {n : ℤ} (hcop : IsCoprime (m : ℤ) n) : χ n ≠ 0 := by
  rw [chi_natAbs_ne_zero_iff]
  have hcopN : Nat.Coprime m n.natAbs := (isCoprime_natAbs_iff m n).mp hcop
  intro h0
  have heuler : n.natAbs ^ m.totient ≡ 1 [MOD m] :=
    Nat.ModEq.pow_totient hcopN.symm
  have htot : 0 < m.totient := Nat.totient_pos.mpr hm
  have hχpow : χ ((n.natAbs ^ m.totient : ℕ) : ℤ) = χ 1 := by
    apply periodic_eq_of_modEq hper
    have hI := Int.natCast_modEq_iff.mpr heuler
    rwa [Nat.cast_one] at hI
  have h0pow : χ ((n.natAbs ^ m.totient : ℕ) : ℤ) = 0 := by
    rw [Nat.cast_pow, map_pow, h0]
    exact zero_pow (ne_of_gt htot)
  rw [map_one] at hχpow
  rw [h0pow] at hχpow
  exact one_ne_zero hχpow.symm

end MonoidHom

namespace MonoidHom

/--
[isDirichletCharacterModulus_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
lemma isDirichletCharacterModulus_iff
  [MonoidWithZero R] [Nontrivial R] [IsCancelMulZero R]
  {χ : ℤ →* R}
  {m m' : ℕ}
-- given
  (hm : 0 < m)
  (hper : Function.Periodic χ (m : ℤ))
  (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d)
  (hm' : 0 < m') :
-- imply
  χ.IsDirichletCharacterModulus m' ↔ m ∣ m' ∧ ∃ k : ℕ, m' ∣ m ^ k := by
-- proof
  constructor
  · intro hchar
    obtain ⟨hper', hnonzero⟩ := hchar
    refine ⟨period_dvd_of_min hm hper hmin hper', ?_⟩
    rw [Nat.exists_dvd_pow_iff (ne_of_gt hm') (ne_of_gt hm)]
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    obtain ⟨hpprime, hpdvd, -⟩ := hp
    refine ⟨hpprime, ?_, ne_of_gt hm⟩
    by_contra hdiv
    have hcop : Nat.Coprime m p := (hpprime.coprime_iff_not_dvd.mpr hdiv).symm
    have hχp : χ (p : ℤ) ≠ 0 := coprime_imp_nonzero hm hper hcop.isCoprime
    have hncop : ¬ IsCoprime ((m' : ℕ) : ℤ) ((p : ℕ) : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact fun hcop' => (hpprime.coprime_iff_not_dvd.mp hcop'.symm) hpdvd
    exact hncop ((hnonzero _).mp hχp)
  · intro hchar
    obtain ⟨hdvd, k, hk⟩ := hchar
    have hper' : Function.Periodic χ ((m' : ℕ) : ℤ) := periodic_of_dvd hper hdvd
    refine ⟨hper', fun n => ?_⟩
    constructor
    · intro hne
      have hcopm := nonzero_imp_coprime hm hper hmin hne
      have hmk : IsCoprime (((m ^ k : ℕ)) : ℤ) n := by
        rwa [Nat.cast_pow]
      exact hmk.of_isCoprime_of_dvd_left (by exact_mod_cast hk)
    · intro hcop
      have hcopm : IsCoprime ((m : ℕ) : ℤ) n :=
        hcop.of_isCoprime_of_dvd_left (by exact_mod_cast hdvd)
      exact coprime_imp_nonzero hm hper hcopm

end MonoidHom

namespace MonoidHom

/--
[isDirichletCharacterModulus_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
lemma isDirichletCharacterModulus_self
  [MonoidWithZero R] [Nontrivial R] [IsCancelMulZero R]
  {χ : ℤ →* R}
  {m : ℕ}
-- given
  (hm : 0 < m)
  (hper : Function.Periodic χ (m : ℤ))
  (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d) :
-- imply
  χ.IsDirichletCharacterModulus m := by
-- proof
  rw [isDirichletCharacterModulus_iff hm hper hmin hm]
  exact ⟨dvd_rfl, 1, by simp⟩

end MonoidHom


-- created on 2026-10-20
-- updated on 2026-10-26
