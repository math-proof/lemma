import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private def pairTerm {K : Type} [NontriviallyNormedField K] (h : ℕ → K) (r : K) (c : PNat × PNat) : K :=
  h (c.2 : ℕ) * r ^ ((c.1 : ℕ) * (c.2 : ℕ))
private def sigmaTerm' {K : Type} [NontriviallyNormedField K] (h : ℕ → K) (r : K) (x : (n : PNat) × Subtype fun p => p ∈ (n : ℕ).divisorsAntidiagonal) : K :=
  h x.2.1.2 * r ^ (x.2.1.1 * x.2.1.2)
private lemma norm_le_of_le_geometric {K : Type} [NontriviallyNormedField K] [CompleteSpace K] {h : ℕ → K} {C : ℝ} {r : K} (hC1 : 1 ≤ C) (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ n.divisorsAntidiagonal) : ‖h p.2 * r ^ (p.1 * p.2)‖ ≤ C ^ n * ‖r‖ ^ n := by
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC1
  obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hp2mem : p.2 ∈ n.divisors := Nat.snd_mem_divisors_of_mem_antidiagonal hp
  have hp2pos : 0 < p.2 := Nat.pos_of_mem_divisors hp2mem
  have hp2le : p.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_divisors hp2mem)
  rw [norm_mul, norm_pow, hmul]
  apply mul_le_mul ((hh p.2 hp2pos).trans (pow_le_pow_right₀ hC1 hp2le)) le_rfl (pow_nonneg (norm_nonneg r) n) (pow_nonneg hC0 n)
private lemma summable_sigmaTerm' {K : Type} [NontriviallyNormedField K] [CompleteSpace K] {h : ℕ → K} {C : ℝ} {r : K} (hC1 : 1 ≤ C) (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) : Summable (sigmaTerm' h r) := by
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC1
  have hs0 : (0 : ℝ) ≤ C * ‖r‖ := mul_nonneg hC0 (norm_nonneg r)
  have hs1 : C * ‖r‖ < 1 := by rwa [mul_comm] at hrC
  have hgeom : Summable fun n : ℕ => (n : ℝ) * (C * ‖r‖) ^ n := by
    have habs : ‖(C * ‖r‖ : ℝ)‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hs0]
    have := summable_pow_mul_geometric_of_norm_lt_one 1 habs
    simpa using this
  have hgeomP : Summable fun n : PNat => ((n : ℕ) : ℝ) * (C * ‖r‖) ^ (n : ℕ) := hgeom.comp_injective PNat.coe_injective
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg (fun a => norm_nonneg _)]
  refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun x => norm_nonneg _) (fun n => ?_) hgeomP
  rw [tsum_fintype]
  calc
    _ = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, ‖h p.2 * r ^ (p.1 * p.2)‖ := by
      rw [Finset.univ_eq_attach]
      apply Finset.sum_attach ((n : ℕ)).divisorsAntidiagonal fun p => ‖h p.2 * r ^ (p.1 * p.2)‖
    _ ≤ ∑ _ ∈ ((n : ℕ)).divisorsAntidiagonal, C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ) := Finset.sum_le_sum fun p hp => norm_le_of_le_geometric hC1 hh hp
    _ = ∑ _ ∈ ((n : ℕ)).divisors, C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ) := by rw [Nat.sum_divisorsAntidiagonal' (f := fun _ _ => C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ))]
    _ = (((n : ℕ)).divisors.card : ℝ) * (C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n : ℕ) : ℝ) * (C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ)) := by
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (pow_nonneg hC0 _) (pow_nonneg (norm_nonneg r) _))
      exact_mod_cast Nat.card_divisors_le_self (n : ℕ)
    _ = ((n : ℕ) : ℝ) * (C * ‖r‖) ^ (n : ℕ) := by rw [mul_pow]
private lemma summable_pairTerm {K : Type} [NontriviallyNormedField K] [CompleteSpace K] {h : ℕ → K} {C : ℝ} {r : K} (hC1 : 1 ≤ C) (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) : Summable (pairTerm h r) := by
  apply (Equiv.summable_iff sigmaAntidiagonalEquivProd).mp
  have hfun : pairTerm h r ∘ ⇑sigmaAntidiagonalEquivProd = sigmaTerm' h r := by
    funext x
    obtain ⟨n, ⟨⟨a, b⟩, hab⟩⟩ := x
    rfl
  rw [hfun]
  apply summable_sigmaTerm' hC1 hh hrC
private lemma tsum_pairTerm_eq_tsum_divisors {K : Type} [NontriviallyNormedField K] [CompleteSpace K] {h : ℕ → K} {C : ℝ} {r : K} (hC1 : 1 ≤ C) (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) : ∑' c : PNat × PNat, pairTerm h r c = ∑' n : PNat, (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ) := by
  have haux := summable_sigmaTerm' (r := r) hC1 hh hrC
  have htrans : ∑' c : PNat × PNat, pairTerm h r c = ∑' x : (n : PNat) × Subtype fun p => p ∈ (n : ℕ).divisorsAntidiagonal, sigmaTerm' h r x := by
    rw [← Equiv.tsum_eq sigmaAntidiagonalEquivProd (pairTerm h r)]
    refine tsum_congr fun x => ?_
    obtain ⟨n, ⟨⟨a, b⟩, hab⟩⟩ := x
    rfl
  rw [htrans, Summable.tsum_sigma haux]
  refine tsum_congr fun n => ?_
  rw [tsum_fintype]
  calc
    _ = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, h p.2 * r ^ (p.1 * p.2) := by
      rw [Finset.univ_eq_attach]
      apply Finset.sum_attach ((n : ℕ)).divisorsAntidiagonal fun p => h p.2 * r ^ (p.1 * p.2)
    _ = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, h p.2 * r ^ (n : ℕ) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
    _ = (∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, h p.2) * r ^ (n : ℕ) := by rw [Finset.sum_mul]
    _ = (∑ d ∈ ((n : ℕ)).divisors, h d) * r ^ (n : ℕ) := by rw [Nat.sum_divisorsAntidiagonal' (f := fun _ d => h d)]
private def succEquivPNat : ℕ ≃ PNat where
  toFun n := n.succPNat
  invFun n := n.natPred
  left_inv n := Nat.natPred_succPNat n
  right_inv n := PNat.succPNat_natPred n
private lemma tsum_succ_prod_main {K : Type} [NontriviallyNormedField K] [CompleteSpace K] {h : ℕ → K} {C : ℝ} {r : K} (hC1 : 1 ≤ C) (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) : ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1)) = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1) := by
  have hL : ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1)) = ∑' c : PNat × PNat, pairTerm h r c := by
    rw [← Equiv.tsum_eq (Equiv.prodCongr succEquivPNat succEquivPNat) (pairTerm h r)]
    refine tsum_congr fun p => ?_
    obtain ⟨a, b⟩ := p
    rfl
  have hR : ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1) = ∑' n : PNat, (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ) := by
    rw [← Equiv.tsum_eq succEquivPNat (fun n : PNat => (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ))]
    apply tsum_congr fun N => rfl
  rw [hL, hR]
  apply tsum_pairTerm_eq_tsum_divisors hC1 hh hrC
private lemma summable_succ_prod {K : Type} [NontriviallyNormedField K] [CompleteSpace K] {h : ℕ → K} {C : ℝ} {r : K} (hC1 : 1 ≤ C) (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) : Summable fun p : ℕ × ℕ => h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1)) := by
  have hsum := summable_pairTerm (r := r) hC1 hh hrC
  have hcomp : Summable (pairTerm h r ∘ ⇑(Equiv.prodCongr succEquivPNat succEquivPNat)) := (Equiv.summable_iff (Equiv.prodCongr succEquivPNat succEquivPNat)).mpr hsum
  refine hcomp.congr fun p => ?_
  obtain ⟨a, b⟩ := p
  rfl
/--
[TateCurve_tsum_succ_prod_eq_tsum_divisors](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_TateCurve_tsum_succ_prod_eq_tsum_divisors.lean)
-/
@[path]
private lemma main
  {K : Type} [NontriviallyNormedField K] [CompleteSpace K]
  {h : ℕ → K}
  {C : ℝ}
  {r : K}
  -- given
  (hC1 : 1 ≤ C)
  (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m)
  (hrC : ‖r‖ * C < 1) :
  -- imply
  ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1)) = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1) :=
  tsum_succ_prod_main hC1 hh hrC


-- created on 2026-10-20
