import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[IsLocalRing_exists_forall_sub_sum_mem_span_pair_of_prime_of_not_associated](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_forall_sub_sum_mem_span_pair_of_prime_of_not_associated.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A] [IsLocalRing A]
  {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
  (ϖ : A)
  (φ : Polynomial A →+* S)
  (χ₀ : S →+* ResidueField A)
  (p : S)
  -- given
  (hϖ : maximalIdeal A = Ideal.span {ϖ})
  (hm : maximalIdeal S = Ideal.span {φ (Polynomial.C ϖ), φ Polynomial.X})
  (hprime : Prime (φ (Polynomial.C ϖ)))
  (hχ₀ : RingHom.ker χ₀ = maximalIdeal S)
  (hχ₀C : ∀ a : A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue A a)
  (hp : Prime p)
  (hpϖ : ¬ Associated p (φ (Polynomial.C ϖ))) :
  -- imply
  ∃ n : ℕ, ∀ x : S, ∃ c : Fin n → A, x - ∑ i, φ (Polynomial.C (c i)) * φ Polynomial.X ^ (i : ℕ) ∈ Ideal.span {p, φ (Polynomial.C ϖ)} := by
  -- proof
  classical
  set ϖ₁ := φ (Polynomial.C ϖ)
  set t := φ Polynomial.X
  have ht𝔪 : t ∈ maximalIdeal S := by
    rw [hm]
    apply Ideal.subset_span (by simp)
  have hϖ𝔪 : ϖ₁ ∈ maximalIdeal S := by
    rw [hm]
    apply Ideal.subset_span (by simp)
  have hpndvd : ¬ ϖ₁ ∣ p := by
    intro h
    obtain ⟨q, hq⟩ := h
    have hdvd : p ∣ ϖ₁ * q := by
      refine ⟨1, ?_⟩
      rw [mul_one]
      apply hq.symm
    obtain h1 | h1 := hp.dvd_or_dvd hdvd
    ·
      obtain ⟨s, hs⟩ := h1
      if hu : IsUnit q then
        obtain ⟨u, rfl⟩ := hu
        exact hpϖ ⟨u⁻¹, by rw [hq, mul_assoc, Units.mul_inv, mul_one]⟩
      else
        apply hprime.ne_zero
        have h2 : ϖ₁ * (1 - q * s) = 0 := by
          have : ϖ₁ = ϖ₁ * (q * s) := by rw [← mul_assoc, ← hq, ← hs]
          linear_combination this
        have hqs : q * s ∈ nonunits S := by
          rw [← IsLocalRing.mem_maximalIdeal]
          apply Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hu)
        obtain ⟨v, hv⟩ := (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hqs).exists_right_inv
        calc
          _ = ϖ₁ * ((1 - q * s) * v) := by rw [hv, mul_one]
          _ = 0 := by rw [← mul_assoc, h2, zero_mul]
    ·
      obtain ⟨r, hr⟩ := h1
      apply hp.ne_zero
      have h2 : p * (1 - ϖ₁ * r) = 0 := by
        have : p = ϖ₁ * (p * r) := by
          rw [← hr]
          apply hq
        linear_combination this
      have hu : IsUnit (1 - ϖ₁ * r) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right _ _ hϖ𝔪)
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      calc
        _ = p * ((1 - ϖ₁ * r) * v) := by rw [hv, mul_one]
        _ = 0 := by rw [← mul_assoc, h2, zero_mul]
  have hdec : ∀ b : S, ¬ IsUnit b → ∃ a b' : S, b = ϖ₁ * a + t * b' := by
    intro b hb
    have : b ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal b).mpr hb
    rw [hm, Ideal.mem_span_pair] at this
    obtain ⟨a, b', h⟩ := this
    refine ⟨a, b', ?_⟩
    rw [← h]
    ring
  have hpow : ∃ n : ℕ, t ^ n ∈ Ideal.span {p, ϖ₁} := by
    by_contra hno
    push Not at hno
    have hnu : ∀ (k : ℕ) (b : S), p - t ^ k * b ∈ Ideal.span {ϖ₁} → ¬ IsUnit b := by
      intro k b hb hu
      apply hno k
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      rw [Ideal.mem_span_pair]
      refine ⟨v, -(c * v), ?_⟩
      have : t ^ k * b = p - ϖ₁ * c := by
        rw [← hc]
        ring
      calc
        _ = (p - ϖ₁ * c) * v := by ring
        _ = t ^ k * b * v := by rw [this]
        _ = t ^ k := by rw [mul_assoc, hv, mul_one]
    have hstep : ∀ (k : ℕ) (b : S), p - t ^ k * b ∈ Ideal.span {ϖ₁} → ∃ b' : S, p - t ^ (k + 1) * b' ∈ Ideal.span {ϖ₁} ∧ b - t * b' ∈ Ideal.span {ϖ₁} := by
      intro k b hb
      obtain ⟨a, b', hdb⟩ := hdec b (hnu k b hb)
      refine ⟨b', ?_, Ideal.mem_span_singleton.mpr ⟨a, by rw [hdb]; ring⟩⟩
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
      apply Ideal.mem_span_singleton.mpr ⟨c + t ^ k * a, by
        have : p = t ^ k * b + ϖ₁ * c := by
          rw [← hc]
          ring
        rw [this, hdb]
        ring⟩
    let T : ℕ → Type _ := fun k => Subtype fun b : S => p - t ^ k * b ∈ Ideal.span {ϖ₁}
    let next : ∀ k, T k → T (k + 1) := fun k b => ⟨(hstep k b.1 b.2).choose, (hstep k b.1 b.2).choose_spec.1⟩
    let g : ∀ k, T k := fun k => Nat.rec (motive := T) ⟨p, by simp⟩ next k
    have hg_succ : ∀ k, (g (k + 1)).1 = (hstep k (g k).1 (g k).2).choose := fun k => rfl
    have hlink : ∀ k, (g k).1 - t * (g (k + 1)).1 ∈ Ideal.span {ϖ₁} := fun k => by
      rw [hg_succ]
      apply (hstep k (g k).1 (g k).2).choose_spec.2
    let J : ℕ → Ideal S := fun k => Ideal.span {(g k).1, ϖ₁}
    have hmono : Monotone J := by
      refine monotone_nat_of_le_succ fun k => ?_
      show Ideal.span {(g k).1, ϖ₁} ≤ Ideal.span {(g (k + 1)).1, ϖ₁}
      rw [Ideal.span_le]
      intro x hx
      obtain rfl | rfl := hx
      ·
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hlink k)
        rw [SetLike.mem_coe, Ideal.mem_span_pair]
        exact ⟨t, c, by linear_combination (-1 : S) * hc⟩
      · apply Ideal.subset_span (by simp)
    obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition (⟨J, hmono⟩ : ℕ →o Ideal S)
    have hmem : (g (N + 1)).1 ∈ J N := by
      have : (g (N + 1)).1 ∈ J (N + 1) := Ideal.subset_span (by simp)
      have hEq : J N = J (N + 1) := hN (N + 1) (Nat.le_succ N)
      rwa [hEq]
    rw [show J N = Ideal.span {(g N).1, ϖ₁} from rfl, Ideal.mem_span_pair] at hmem
    obtain ⟨c, d, hcd⟩ := hmem
    obtain ⟨e₀, he₀⟩ := Ideal.mem_span_singleton.mp (hlink N)
    have hunit : IsUnit (1 - c * t) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_left _ c ht𝔪)
    obtain ⟨v, hv⟩ := hunit.exists_right_inv
    have hgN1 : (g (N + 1)).1 ∈ Ideal.span {ϖ₁} := by
      have h1 : (g (N + 1)).1 * (1 - c * t) = ϖ₁ * (c * e₀ + d) := by
        have hgN : (g N).1 = t * (g (N + 1)).1 + ϖ₁ * e₀ := by
          rw [← he₀]
          ring
        have := hcd
        rw [hgN] at this
        linear_combination (-1 : S) * this
      have : (g (N + 1)).1 = ϖ₁ * (c * e₀ + d) * v := by rw [← h1, mul_assoc, hv, mul_one]
      rw [this]
      apply Ideal.mem_span_singleton.mpr ⟨(c * e₀ + d) * v, by ring⟩
    apply hpndvd
    have hp1 := (g (N + 1)).2
    obtain ⟨c₁, hc₁⟩ := Ideal.mem_span_singleton.mp hp1
    obtain ⟨c₂, hc₂⟩ := Ideal.mem_span_singleton.mp hgN1
    exact ⟨c₁ + t ^ (N + 1) * c₂, by
      have : p = t ^ (N + 1) * (g (N + 1)).1 + ϖ₁ * c₁ := by
        rw [← hc₁]
        ring
      rw [this, hc₂]
      ring⟩
  obtain ⟨n, hn⟩ := hpow
  have hpeel : ∀ (k : ℕ) (x : S), ∃ (c : Fin k → A) (r w : S), x = ∑ i, φ (Polynomial.C (c i)) * t ^ (i : ℕ) + t ^ k * r + ϖ₁ * w := by
    intro k
    induction k
    ·
      intro x
      exact ⟨Fin.elim0, x, 0, by simp⟩
    ·
      rename_i k ih
      intro x
      obtain ⟨c, r, w, hx⟩ := ih x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (χ₀ r)
      have hr𝔪 : r - φ (Polynomial.C a) ∈ maximalIdeal S := by
        rw [← hχ₀, RingHom.mem_ker, map_sub, hχ₀C, sub_eq_zero]
        apply ha.symm
      rw [hm, Ideal.mem_span_pair] at hr𝔪
      obtain ⟨y, z, hyz⟩ := hr𝔪
      refine ⟨Fin.snoc c a, z, w + t ^ k * y, ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
      have hr : r = φ (Polynomial.C a) + y * ϖ₁ + z * t := by linear_combination (-1 : S) * hyz
      rw [hx, hr, pow_succ]
      ring
  refine ⟨n, fun x => ?_⟩
  obtain ⟨c, r, w, hx⟩ := hpeel n x
  refine ⟨c, ?_⟩
  have : x - ∑ i, φ (Polynomial.C (c i)) * t ^ (i : ℕ) = t ^ n * r + ϖ₁ * w := by
    rw [hx]
    ring
  rw [this]
  refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hn) ?_
  apply Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))


-- created on 2026-10-20
