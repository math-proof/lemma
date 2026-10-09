import Mathlib
import sympy.Basic


/--
[AlgHom_comp_injective_and_exists_comp_eq_iff_of_sub_one_mem_span_of_mul_sub_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_comp_injective_and_exists_comp_eq_iff_of_sub_one_mem_span_of_mul_sub_eq_zero.lean)
-/

private lemma algebraMap_intCast
  {S : Type*}
  [CommRing S]
  [Algebra ℤ S]
  (z : ℤ) :
  algebraMap ℤ S z = (z : S) :=
  eq_intCast (algebraMap ℤ S) z

private lemma exists_mul_add_eq_one_of_sub_one_mem_span
  {S : Type*}
  [CommRing S]
  {p : ℕ}
  (b : S)
  (n : ℕ)
  (hb : b - 1 ∈ Ideal.span {(p : S)}) :
  ∃ u v : S, u * (p : S) ^ n + v * b = 1 := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
  have hcp : IsCoprime (p : S) b := ⟨-c, 1, by linear_combination (-1 : S) * hc⟩
  obtain ⟨u, v, huv⟩ := IsCoprime.pow_left (m := n) hcp
  exact ⟨u, v, huv⟩

@[path]
private lemma main
  [CommRing R]
  {A K : Type} [CommRing A] [CommRing K] [Algebra ℤ A] [Algebra ℤ K]
  {ι : AlgHom ℤ A K}
  {ε : AlgHom ℤ K ℤ}
  {p : ℕ}
  {a : K}
-- given
  (hι : Function.Injective ι)
  (_ : ∀ k : K, (p : K) * k = 0 → k = 0)
  (h1 : a - 1 ∈ Ideal.span {(p : K)})
  (h2 : ∀ k : K, a * (k - algebraMap ℤ K (ε k)) = 0)
  (h3 : ∀ k : K, ∃ (n : ℕ) (h : A), (p : K) ^ n * k = ι h) :
-- imply
  (∀ f g : AlgHom ℤ K R, f.comp ι = g.comp ι → f = g) ∧
      ∀ g : AlgHom ℤ A R, (∃ f : AlgHom ℤ K R, f.comp ι = g) ↔
        ∃ b : R, b - 1 ∈ Ideal.span {(p : R)} ∧
          ∀ h : A, b * (g h - algebraMap ℤ R (ε (ι h))) = 0 := by
-- proof
  classical
  have hεk : ∀ (k : K) (n : ℕ) (h : A), (p : K) ^ n * k = ι h →
      ((ε (ι h) : ℤ) : R) = (p : R) ^ n * ((ε k : ℤ) : R) := by
    intro k n h hk
    have := congrArg ε hk.symm
    rw [map_mul, map_pow, map_natCast] at this
    rw [this]; push_cast; ring

  have hfa : ∀ φ : AlgHom ℤ K R, φ a - 1 ∈ Ideal.span {(p : R)} := by
    intro φ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
    refine Ideal.mem_span_singleton'.2 ⟨φ c, ?_⟩
    have := congrArg φ hc
    rwa [map_mul, map_natCast, map_sub, map_one] at this
  have hea : ∀ (φ : AlgHom ℤ K R) (k : K), φ a * φ k = φ a * ((ε k : ℤ) : R) := by
    intro φ k
    have := congrArg φ (h2 k)
    rw [map_mul, map_sub, map_zero, AlgHom.commutes, algebraMap_intCast] at this
    linear_combination this
  have hpk : ∀ (φ : AlgHom ℤ K R) (k : K) (n : ℕ) (h : A), (p : K) ^ n * k = ι h →
      (p : R) ^ n * φ k = φ (ι h) := by
    intro φ k n h hk
    rw [← hk, map_mul, map_pow, map_natCast]
  refine ⟨fun f f' hff' => ?_, fun g => ⟨?_, ?_⟩⟩
  ·
    apply AlgHom.ext
    intro k
    obtain ⟨n, h, hk⟩ := h3 k
    have e1 : (p : R) ^ n * (f k - f' k) = 0 := by
      rw [mul_sub, hpk f k n h hk, hpk f' k n h hk, ← AlgHom.comp_apply, hff', AlgHom.comp_apply,
        sub_self]
    have e2 : (f a * f' a) * (f k - f' k) = 0 := by
      linear_combination (f' a) * hea f k - (f a) * hea f' k
    have hprod : f a * f' a - 1 ∈ Ideal.span {(p : R)} := by
      have := Ideal.add_mem _ (Ideal.mul_mem_left _ (f a) (hfa f')) (hfa f)
      convert this using 1
      ring
    obtain ⟨u, v, huv⟩ := exists_mul_add_eq_one_of_sub_one_mem_span (f a * f' a) n hprod
    apply sub_eq_zero.1
    linear_combination -(f k - f' k) * huv + u * e1 + v * e2
  ·
    rintro ⟨f, hf⟩
    refine ⟨f a, hfa f, fun h => ?_⟩
    have := hea f (ι h)
    rw [algebraMap_intCast, ← hf, AlgHom.comp_apply]
    linear_combination this
  ·
    rintro ⟨b, hb1, hb2⟩
    have hb2' : ∀ h : A, b * g h = b * ((ε (ι h) : ℤ) : R) := by
      intro h
      have := hb2 h
      rw [algebraMap_intCast] at this
      linear_combination this

    let P : K → R → Prop := fun k r =>
      (∃ (n : ℕ) (h : A), (p : K) ^ n * k = ι h ∧ (p : R) ^ n * r = g h) ∧ b * r = b * ((ε k : ℤ) : R)
    have hPex : ∀ k : K, ∃ r : R, P k r := by
      intro k
      obtain ⟨n, h, hk⟩ := h3 k
      obtain ⟨u, v, huv⟩ := exists_mul_add_eq_one_of_sub_one_mem_span b n hb1
      refine ⟨u * g h + v * b * ((ε k : ℤ) : R), ⟨n, h, hk, ?_⟩, ?_⟩
      ·
        linear_combination g h * huv - v * hb2' h - v * b * hεk k n h hk
      ·
        linear_combination b * ((ε k : ℤ) : R) * huv + u * hb2' h + u * b * hεk k n h hk
    have hPuniq : ∀ (k : K) (r₁ r₂ : R), P k r₁ → P k r₂ → r₁ = r₂ := by
      rintro k r₁ r₂ ⟨⟨n₁, h₁, hk₁, hr₁⟩, hb₁⟩ ⟨⟨n₂, h₂, hk₂, hr₂⟩, hb₂⟩
      have hA : (p : A) ^ n₂ * h₁ = (p : A) ^ n₁ * h₂ := by
        apply hι
        rw [map_mul, map_pow, map_natCast, ← hk₁, map_mul, map_pow, map_natCast, ← hk₂]
        ring
      have e1 : (p : R) ^ (n₁ + n₂) * (r₁ - r₂) = 0 := by
        have hg := congrArg g hA
        rw [map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast] at hg
        rw [pow_add]
        linear_combination (p : R) ^ n₂ * hr₁ - (p : R) ^ n₁ * hr₂ + hg
      have e2 : b * (r₁ - r₂) = 0 := by rw [mul_sub, hb₁, hb₂, sub_self]
      obtain ⟨u, v, huv⟩ := exists_mul_add_eq_one_of_sub_one_mem_span b (n₁ + n₂) hb1
      apply sub_eq_zero.1
      linear_combination -(r₁ - r₂) * huv + u * e1 + v * e2

    let F : K → R := fun k => Classical.choose (hPex k)
    have hF : ∀ k, P k (F k) := fun k => Classical.choose_spec (hPex k)
    have hFeq : ∀ (k : K) (r : R), P k r → F k = r := fun k r hr => hPuniq k _ _ (hF k) hr
    have hF1 : F 1 = 1 := hFeq 1 1 ⟨⟨0, 1, by simp, by simp⟩, by simp⟩
    have hF0 : F 0 = 0 := hFeq 0 0 ⟨⟨0, 0, by simp, by simp⟩, by simp⟩
    have hFmul : ∀ x y : K, F (x * y) = F x * F y := by
      intro x y
      obtain ⟨⟨n₁, h₁, hk₁, hr₁⟩, hb₁⟩ := hF x
      obtain ⟨⟨n₂, h₂, hk₂, hr₂⟩, hb₂⟩ := hF y
      refine hFeq _ _ ⟨⟨n₁ + n₂, h₁ * h₂, ?_, ?_⟩, ?_⟩
      ·
        rw [map_mul, ← hk₁, ← hk₂]
        ring
      ·
        rw [map_mul, ← hr₁, ← hr₂]
        ring
      ·
        calc _
          _ = (b * F x) * F y := by ring
          _ = ((ε x : ℤ) : R) * (b * F y) := by rw [hb₁]; ring
          _ = b * ((ε (x * y) : ℤ) : R) := by rw [hb₂, map_mul]; push_cast; ring
    have hFadd : ∀ x y : K, F (x + y) = F x + F y := by
      intro x y
      obtain ⟨⟨n₁, h₁, hk₁, hr₁⟩, hb₁⟩ := hF x
      obtain ⟨⟨n₂, h₂, hk₂, hr₂⟩, hb₂⟩ := hF y
      refine hFeq _ _ ⟨⟨n₁ + n₂, (p : A) ^ n₂ * h₁ + (p : A) ^ n₁ * h₂, ?_, ?_⟩, ?_⟩
      ·
        rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, ← hk₁, ← hk₂]
        ring
      ·
        rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, ← hr₁, ← hr₂]
        ring
      ·
        rw [mul_add, hb₁, hb₂, map_add]
        push_cast
        ring
    let Fr : K →+* R :=
      { toFun := F, map_one' := hF1, map_mul' := hFmul, map_zero' := hF0, map_add' := hFadd }
    let f : AlgHom ℤ K R :=
      { Fr with
        commutes' := fun z => by
          change F (algebraMap ℤ K z) = algebraMap ℤ R z
          rw [algebraMap_intCast, algebraMap_intCast]
          exact map_intCast Fr z }
    refine ⟨f, ?_⟩
    apply AlgHom.ext
    intro h
    change F (ι h) = g h
    exact hFeq _ _ ⟨⟨0, h, by simp, by simp⟩, hb2' h⟩


-- created on 2026-10-09
