import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.CarmichaelNumber


/--
[Nat.isCarmichaelNumber_iff_zmod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CarmichaelNumber.lean)
-/
@[path]
lemma Nat.isCarmichaelNumber_iff_zmod
  {n : ℕ} :
-- imply
  Nat.IsCarmichaelNumber n ↔
    1 < n ∧ ¬n.Prime ∧ ∀ x : ZMod n, x ^ n = x := by
-- proof
  constructor
  · rintro ⟨hn, hNotPrime, hUniv⟩
    let _ : NeZero n := ⟨by omega⟩
    refine ⟨hn, hNotPrime, fun x ↦ ?_⟩
    have hCast : ((x.val ^ n : ℕ) : ZMod n) = ((x.val : ℕ) : ZMod n) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hUniv x.val)
    rwa [← ZMod.natCast_zmod_val x, ← Nat.cast_pow]
  · rintro ⟨hn, hNotPrime, hUniv⟩
    refine ⟨hn, hNotPrime, fun a ↦ ?_⟩
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa using hUniv (a : ZMod n)

/--
[carmichael_prime_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CarmichaelNumber.lean)
-/
@[path]
private lemma carmichael_prime_eq (p : ℕ) (hp : p.Prime) :
  ArithmeticFunction.carmichael p = p - 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h1 : ArithmeticFunction.carmichael (2 ^ 1) = 2 ^ (1 - 1) := by
      apply ArithmeticFunction.carmichael_two_pow_of_le_two
      decide
    simpa using h1
  · have h : ArithmeticFunction.carmichael (p ^ 1) = (p ^ 1).totient :=
    ArithmeticFunction.carmichael_pow_of_prime_ne_two 1 hp hp2
    simp only [pow_one] at h
    rw [h, Nat.totient_prime hp]

/--
[Nat.isCarmichaelNumber_iff_korselt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CarmichaelNumber.lean)
-/
@[path]
lemma Nat.isCarmichaelNumber_iff_korselt
  {n : ℕ}
-- given
  (hn : 1 < n) :
-- imply
  Nat.IsCarmichaelNumber n ↔
    Squarefree n ∧
    (∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)) ∧ ¬n.Prime := by
-- proof
  constructor
  · intro hCarmichael
    have hNotPrime : ¬n.Prime := hCarmichael.2.1
    have hUnivZMod : ∀ x : ZMod n, x ^ n = x :=
      ((Nat.isCarmichaelNumber_iff_zmod n).mp hCarmichael).2.2
    have hn0 : n ≠ 0 := by omega
    have _ : NeZero n := ⟨hn0⟩
    have hIsReduced : IsReduced (ZMod n) := by
      rw [isReduced_iff_pow_one_lt n hn]
      intro x hx
      have hPowEq : x ^ n = x := hUnivZMod x
      rwa [hPowEq] at hx
    have hSF : Squarefree n := by
      have h := (isReduced_zmod (n := n)).mp hIsReduced
      obtain h | h := h
      · exact h
      · omega
    refine ⟨hSF, ?_, hNotPrime⟩
    have hCarmDvd : ArithmeticFunction.carmichael n ∣ (n - 1) := by
      rw [ArithmeticFunction.carmichael_eq_exponent hn0,
        Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro u
      let xu : ZMod n := (u : ZMod n)
      have hEq : xu ^ n = xu := hUnivZMod xu
      have hUN : u ^ n = u := by
        apply Units.ext
        show (↑(u ^ n) : ZMod n) = (↑u : ZMod n)
        rwa [Units.val_pow_eq_pow_val]
      have hn_eq : n = (n - 1) + 1 := by omega
      have hPow : u ^ ((n - 1) + 1) = u := by rw [← hn_eq]; exact hUN
      rw [pow_succ] at hPow
      have h1 : u ^ (n - 1) * u = 1 * u := by rw [hPow, one_mul]
      exact mul_right_cancel h1
    intro p hp hpn
    have h1 : ArithmeticFunction.carmichael p ∣ ArithmeticFunction.carmichael n :=
      ArithmeticFunction.carmichael_dvd hpn
    have h2 : ArithmeticFunction.carmichael p = p - 1 := carmichael_prime_eq p hp
    rw [h2] at h1
    exact dvd_trans h1 hCarmDvd
  · rintro ⟨hSF, hDiv, hNotPrime⟩
    refine ⟨hn, hNotPrime, ?_⟩
    intro a
    have hLe : a ≤ a ^ n := by
      by_cases ha0 : a = 0
      · simp [ha0]
      · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
        exact le_self_pow₀ ha1 (by omega)
    have hDvdPerPrime : ∀ p ∈ n.primeFactors, p ∣ a ^ n - a := by
      intro p hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hPP : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hDivP : (p - 1) ∣ (n - 1) := hDiv p hpPrime hPP
      by_cases hDvd : p ∣ a
      · have hPowDvd : p ∣ a ^ n := dvd_pow hDvd (by omega)
        have h1 : a ^ n ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hPowDvd
        have h2 : a ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hDvd
        have h3 : a ^ n ≡ a [MOD p] := h1.trans h2.symm
        exact h3.symm.dvd'
      · have hCop : Nat.Coprime a p := (hpPrime.coprime_iff_not_dvd.mpr hDvd).symm
        have hFermat : a ^ (p - 1) ≡ 1 [MOD p] :=
          Nat.ModEq.pow_card_sub_one_eq_one hpPrime hCop
        have hPowOne : a ^ (n - 1) ≡ 1 [MOD p] := by
          obtain ⟨k, hk⟩ := hDivP
          have hn1_eq : n - 1 = (p - 1) * k := by omega
          rw [hn1_eq]
          have h1 : a ^ ((p - 1) * k) = (a ^ (p - 1)) ^ k := by rw [pow_mul]
          rw [h1]
          calc
            (a ^ (p - 1)) ^ k ≡ 1 ^ k [MOD p] := hFermat.pow k
            _ = 1 := by simp
        have hn_eq : n = (n - 1) + 1 := by omega
        have hGoal : a ^ n ≡ a [MOD p] := by
          conv_lhs => rw [hn_eq, pow_succ]
          have hMul : a ^ (n - 1) * a ≡ 1 * a [MOD p] :=
            hPowOne.mul (Nat.ModEq.refl a)
          simp only [one_mul] at hMul
          exact hMul
        exact hGoal.symm.dvd'
    let d := a ^ n - a
    have hProdDvd : n ∣ d := by
      by_cases hd0 : d = 0
      · simp [hd0]
      · have hProd : (∏ p ∈ n.primeFactors, p) ∣ d := by
        apply (Nat.prod_primeFactors_dvd_iff hd0).mpr
        intro p hp
        have hmem : p ∈ d.primeFactors :=
          Nat.mem_primeFactors.mpr
            ⟨Nat.prime_of_mem_primeFactors hp, hDvdPerPrime p hp, hd0⟩
        exact hmem
        rwa [Nat.prod_primeFactors_of_squarefree hSF] at hProd
    exact (Nat.modEq_of_dvd' hLe hProdDvd).symm


-- created on 2026-10-20
-- updated on 2026-10-26
