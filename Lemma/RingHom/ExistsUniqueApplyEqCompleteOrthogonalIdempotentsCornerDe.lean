import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma e_mul_eq_zero {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι] {e : ι → K} {χ : ι → (K →+* ℚ)} (hχe : ∀ a b : ι, χ b (e a) = if b = a then 1 else 0) (hsep : ∀ k k' : K, (∀ a, χ a k = χ a k') → k = k') {a : ι} {k : K} (hk : χ a k = 0) : e a * k = 0 := by
  apply hsep
  intro b
  rw [map_mul, hχe, map_zero]
  if h : b = a then
    subst h
    rw [ite_eq_left rfl, hk, mul_zero]
  else
    rw [ite_eq_right h, zero_mul]

private abbrev B {K : Type} [CommRing K] {ι : Type} (χ : ι → (K →+* ℚ)) (a : ι) : Subring ℚ := (χ a).range

private abbrev ρ {K : Type} [CommRing K] {ι : Type} (χ : ι → (K →+* ℚ)) (a : ι) : K →+* B χ a := (χ a).rangeRestrict

private lemma ρ_surjective {K : Type} [CommRing K] {ι : Type} {χ : ι → (K →+* ℚ)} (a : ι) : Function.Surjective (ρ χ a) := (χ a).rangeRestrict_surjective

private lemma coe_ρ {K : Type} [CommRing K] {ι : Type} {χ : ι → (K →+* ℚ)} (a : ι) (k : K) : (ρ χ a k : ℚ) = χ a k := rfl

private lemma ker_ρ {K : Type} [CommRing K] {ι : Type} {χ : ι → (K →+* ℚ)} (a : ι) : RingHom.ker (ρ χ a) = RingHom.ker (χ a) := by
  ext k
  rw [RingHom.mem_ker, RingHom.mem_ker, ← Subtype.coe_inj]
  rfl

private lemma isLocalization_B {K : Type} [CommRing K] {ι : Type} {χ : ι → (K →+* ℚ)} {d : ι → ℕ} (hd : ∀ a, 0 < d a) (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n) (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹) (a : ι) : IsLocalization.Away ((d a : ℤ)) (B χ a) := by
  have hd0 : ((d a : ℚ)) ≠ 0 := by
    exact_mod_cast (hd a).ne'
  obtain ⟨y, hy⟩ := hinv a
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  ·
    intro u
    obtain ⟨n, hn⟩ := u.2
    refine IsUnit.of_mul_eq_one (b := ρ χ a (y ^ n)) (Subtype.ext ?_)
    rw [hn]
    change ((algebraMap ℤ (B χ a) ((d a : ℤ) ^ n) : B χ a) : ℚ) * χ a (y ^ n) = 1
    rw [map_pow (χ a), hy, map_pow]
    change (((d a : ℤ) : B χ a) : ℚ) ^ n * _ = 1
    push_cast
    rw [← mul_pow, mul_inv_cancel₀ hd0, one_pow]
  ·
    intro w
    obtain ⟨k, hk⟩ := w.2
    obtain ⟨n, m, hm⟩ := hval a k
    refine ⟨(m, ⟨(d a : ℤ) ^ n, n, rfl⟩), Subtype.ext ?_⟩
    rw [← hk]
    change χ a k * (((d a : ℤ) ^ n : ℤ) : ℚ) = (m : ℚ)
    rw [hm]
    push_cast
    field_simp
  ·
    intro x x' hxx'
    refine ⟨1, ?_⟩
    have : (x : ℚ) = x' := by
      have := congrArg (fun z : B χ a => (z : ℚ)) hxx'
      simpa using this
    simp only [OneMemClass.coe_one, one_mul]
    exact_mod_cast this

private noncomputable def I {T : Type} [CommRing T] {ι : Type} (b : ι → T) (a : ι) : Ideal T := Ideal.span {1 - b a}

private lemma one_sub_mem_I {T : Type} [CommRing T] {ι : Type} {b : ι → T} (a : ι) : 1 - b a ∈ I b a := Ideal.subset_span rfl

private lemma b_mem_I {T : Type} [CommRing T] {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → T} (hb : CompleteOrthogonalIdempotents b) {a a' : ι} (h : a' ≠ a) : b a' ∈ I b a := by
  have : b a' = b a' * (1 - b a) := by
    rw [mul_sub, mul_one, hb.ortho h, sub_zero]
  rw [this]
  exact Ideal.mul_mem_left _ _ (one_sub_mem_I a)

private lemma mk_b {T : Type} [CommRing T] {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → T} {a a' : ι} (hb : CompleteOrthogonalIdempotents b) : Ideal.Quotient.mk (I b a) (b a') = if a = a' then 1 else 0 := by
  if h : a = a' then
    subst h
    rw [ite_eq_left rfl, eq_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk (I b a)), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (one_sub_mem_I a)
  else
    rw [ite_eq_right h]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (b_mem_I hb (Ne.symm h))

private lemma isCoprime_I {T : Type} [CommRing T] {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → T} (hb : CompleteOrthogonalIdempotents b) : Pairwise (Function.onFun IsCoprime (I b)) := by
  intro a a' h
  rw [Function.onFun, Ideal.isCoprime_iff_exists]
  exact ⟨1 - b a, one_sub_mem_I a, b a, b_mem_I hb h, by ring⟩

private lemma iInf_I {T : Type} [CommRing T] {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → T} (hb : CompleteOrthogonalIdempotents b) : ⨅ a, I b a = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  have hxb : ∀ a, x * b a = 0 := by
    intro a
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_iInf.mp hx a)
    rw [← ht, mul_assoc, sub_mul, one_mul, hb.idem a, sub_self, mul_zero]
  calc
    _ = x * ∑ a, b a := by
      rw [hb.complete, mul_one]
    _ = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun a _ => hxb a

private noncomputable def πT {T : Type} [CommRing T] {ι : Type} [Fintype ι] (b : ι → T) : T →+* ∀ a, T ⧸ I b a := RingHom.pi fun a => Ideal.Quotient.mk (I b a)

private lemma πT_apply {T : Type} [CommRing T] {ι : Type} [Fintype ι] {b : ι → T} {t : T} {a : ι} : πT b t a = Ideal.Quotient.mk (I b a) t := rfl

private lemma πT_injective {T : Type} [CommRing T] {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → T} (hb : CompleteOrthogonalIdempotents b) : Function.Injective (πT b) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  have : t ∈ ⨅ a, I b a := by
    exact Ideal.mem_iInf.mpr fun a => Ideal.Quotient.eq_zero_iff_mem.mp (congrFun ht a)
  rwa [iInf_I hb, Ideal.mem_bot] at this

private lemma πT_surjective {T : Type} [CommRing T] {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → T} (hb : CompleteOrthogonalIdempotents b) : Function.Surjective (πT b) := by
  intro y
  obtain ⟨xbar, hx⟩ := Ideal.quotientInfToPiQuotient_surj (isCoprime_I hb) y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
  refine ⟨x, ?_⟩
  rw [← hx]
  funext a
  rw [πT_apply, Ideal.quotientInfToPiQuotient_mk']

private lemma isUnit_d {T : Type} [CommRing T] {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → T} {d : ι → ℕ} (hb : CompleteOrthogonalIdempotents b) (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a) (a : ι) : IsUnit ((Int.castRingHom (T ⧸ I b a)) (d a : ℤ)) := by
  obtain ⟨v, hv⟩ := hbd a
  refine IsUnit.of_mul_eq_one_right (a := Ideal.Quotient.mk (I b a) v) ?_
  have h1 : Ideal.Quotient.mk (I b a) (b a) = 1 := by
    rw [mk_b hb, ite_eq_left rfl]
  have := congrArg (Ideal.Quotient.mk (I b a)) hv
  rw [map_mul, map_mul, h1, mul_one, map_natCast] at this
  simpa using this

private noncomputable def f {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → (K →+* ℚ)} {d : ι → ℕ} {T : Type} [CommRing T] {b : ι → T} (hd : ∀ a, 0 < d a) (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n) (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹) (hb : CompleteOrthogonalIdempotents b) (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a) (a : ι) : K →+* T ⧸ I b a :=
  let _ := isLocalization_B hd hval hinv a
  (IsLocalization.Away.lift ((d a : ℤ)) (isUnit_d hb hbd a)).comp (ρ χ a)

private lemma f_apply_of_eq_intCast {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → (K →+* ℚ)} {d : ι → ℕ} {T : Type} [CommRing T] {b : ι → T} (hd : ∀ a, 0 < d a) (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n) (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹) (hb : CompleteOrthogonalIdempotents b) (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a) (a : ι) (k : K) (m : ℤ) (hk : χ a k = m) : f hd hval hinv hb hbd a k = m := by
  let _ := isLocalization_B hd hval hinv a
  have hρ : ρ χ a k = algebraMap ℤ (B χ a) m := by
    apply Subtype.ext
    rw [coe_ρ a k, hk]
    rfl
  change IsLocalization.Away.lift ((d a : ℤ)) (isUnit_d hb hbd a) (ρ χ a k) = _
  rw [hρ, IsLocalization.Away.lift_eq]
  simp

private lemma f_e {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι] {e : ι → K} {χ : ι → (K →+* ℚ)} {d : ι → ℕ} {T : Type} [CommRing T] {b : ι → T} (hχe : ∀ a b : ι, χ b (e a) = if b = a then 1 else 0) (hd : ∀ a, 0 < d a) (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n) (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹) (hb : CompleteOrthogonalIdempotents b) (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a) (a c : ι) : f hd hval hinv hb hbd a (e c) = if a = c then 1 else 0 := by
  if h : a = c then
    have hk : χ a (e c) = 1 := by
      rw [hχe, ite_eq_left h]
    rw [ite_eq_left h, f_apply_of_eq_intCast (hd := hd) (hval := hval) (hinv := hinv) (hb := hb) (hbd := hbd) (m := 1) a (e c) hk]
    simp
  else
    have hk : χ a (e c) = 0 := by
      rw [hχe, ite_eq_right h]
    rw [ite_eq_right h, f_apply_of_eq_intCast (hd := hd) (hval := hval) (hinv := hinv) (hb := hb) (hbd := hbd) (m := 0) a (e c) hk]
    simp

private noncomputable def φ {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → (K →+* ℚ)} {d : ι → ℕ} {T : Type} [CommRing T] {b : ι → T} (hd : ∀ a, 0 < d a) (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n) (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹) (hb : CompleteOrthogonalIdempotents b) (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a) : K →+* T :=
  ((RingEquiv.ofBijective (πT b) ⟨πT_injective hb, πT_surjective hb⟩).symm : (∀ a, T ⧸ I b a) →+* T).comp (RingHom.pi fun a => f hd hval hinv hb hbd a)

private lemma πT_φ {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → (K →+* ℚ)} {d : ι → ℕ} {T : Type} [CommRing T] {b : ι → T} (hd : ∀ a, 0 < d a) (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n) (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹) (hb : CompleteOrthogonalIdempotents b) (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a) (k : K) : πT b (φ hd hval hinv hb hbd k) = fun a => f hd hval hinv hb hbd a k := by
  set E := RingEquiv.ofBijective (πT b) ⟨πT_injective hb, πT_surjective hb⟩ with hE
  have hEapp : ∀ t, πT b t = E t := fun t => rfl
  change πT b (E.symm ((RingHom.pi fun a => f hd hval hinv hb hbd a) k)) = _
  rw [hEapp, RingEquiv.apply_symm_apply]
  rfl

private lemma φ_e {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι] {e : ι → K} {χ : ι → (K →+* ℚ)} {d : ι → ℕ} {T : Type} [CommRing T] {b : ι → T} (hχe : ∀ a b : ι, χ b (e a) = if b = a then 1 else 0) (hd : ∀ a, 0 < d a) (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n) (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹) (hb : CompleteOrthogonalIdempotents b) (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a) (c : ι) : φ hd hval hinv hb hbd (e c) = b c := by
  apply πT_injective hb
  rw [πT_φ]
  funext a
  rw [f_e hχe hd hval hinv hb hbd a c, πT_apply, mk_b hb]

private lemma ker_le_of_apply_e {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι] {e : ι → K} (he : CompleteOrthogonalIdempotents e) {χ : ι → (K →+* ℚ)} (hχe : ∀ a b : ι, χ b (e a) = if b = a then 1 else 0) (hsep : ∀ k k' : K, (∀ a, χ a k = χ a k') → k = k') {T : Type} [CommRing T] {b : ι → T} (hb : CompleteOrthogonalIdempotents b) {φ' : K →+* T} (hφ' : ∀ a, φ' (e a) = b a) (a : ι) : RingHom.ker (ρ χ a) ≤ RingHom.ker ((Ideal.Quotient.mk (I b a)).comp φ') := by
  intro k hk
  rw [ker_ρ a, RingHom.mem_ker] at hk
  rw [RingHom.mem_ker, RingHom.comp_apply]
  have hek : e a * k = 0 := e_mul_eq_zero hχe hsep hk
  have hk' : k = ∑ c, e c * k := by
    rw [← Finset.sum_mul, he.complete, one_mul]
  rw [hk', map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro c _
  if hc : c = a then
    subst hc
    rw [hek, map_zero, map_zero]
  else
    rw [map_mul, map_mul, hφ', mk_b hb, ite_eq_right (Ne.symm hc), zero_mul]

private lemma mk_comp_eq {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι] {e : ι → K} (he : CompleteOrthogonalIdempotents e) {χ : ι → (K →+* ℚ)} (hχe : ∀ a b : ι, χ b (e a) = if b = a then 1 else 0) (hsep : ∀ k k' : K, (∀ a, χ a k = χ a k') → k = k') {d : ι → ℕ} (hd : ∀ a, 0 < d a) (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n) (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹) {T : Type} [CommRing T] {b : ι → T} (hb : CompleteOrthogonalIdempotents b) {φ₁ φ₂ : K →+* T} (h₁ : ∀ a, φ₁ (e a) = b a) (h₂ : ∀ a, φ₂ (e a) = b a) (a : ι) : (Ideal.Quotient.mk (I b a)).comp φ₁ = (Ideal.Quotient.mk (I b a)).comp φ₂ := by
  let _ := isLocalization_B hd hval hinv a
  set L := (ρ χ a).liftOfSurjective (C := T ⧸ I b a) (ρ_surjective a) with hL
  set g₁ := L ⟨(Ideal.Quotient.mk (I b a)).comp φ₁, ker_le_of_apply_e he hχe hsep hb h₁ a⟩
  set g₂ := L ⟨(Ideal.Quotient.mk (I b a)).comp φ₂, ker_le_of_apply_e he hχe hsep hb h₂ a⟩
  have hg₁ : g₁.comp (ρ χ a) = (Ideal.Quotient.mk (I b a)).comp φ₁ := (ρ χ a).liftOfSurjective_comp (ρ_surjective a) _
  have hg₂ : g₂.comp (ρ χ a) = (Ideal.Quotient.mk (I b a)).comp φ₂ := (ρ χ a).liftOfSurjective_comp (ρ_surjective a) _
  have hg : g₁ = g₂ := IsLocalization.ringHom_ext (Submonoid.powers ((d a : ℤ))) (RingHom.ext_int _ _)
  rw [← hg₁, ← hg₂, hg]

private lemma eq_of_apply_e {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι] {e : ι → K} (he : CompleteOrthogonalIdempotents e) {χ : ι → (K →+* ℚ)} (hχe : ∀ a b : ι, χ b (e a) = if b = a then 1 else 0) (hsep : ∀ k k' : K, (∀ a, χ a k = χ a k') → k = k') {d : ι → ℕ} (hd : ∀ a, 0 < d a) (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n) (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹) {T : Type} [CommRing T] {b : ι → T} (hb : CompleteOrthogonalIdempotents b) {φ₁ φ₂ : K →+* T} (h₁ : ∀ a, φ₁ (e a) = b a) (h₂ : ∀ a, φ₂ (e a) = b a) : φ₁ = φ₂ := by
  refine RingHom.ext fun k => πT_injective hb (funext fun a => ?_)
  rw [πT_apply, πT_apply]
  exact congrArg (fun g : K →+* T ⧸ I b a => g k) (mk_comp_eq he hχe hsep hd hval hinv hb h₁ h₂ a)

/--
[RingHom_existsUnique_apply_eq_of_completeOrthogonalIdempotents_of_corner_denominators](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_existsUnique_apply_eq_of_completeOrthogonalIdempotents_of_corner_denominators.lean)
-/
@[path]
private lemma main
  (K : Type) [CommRing K]
  (ι : Type) [Fintype ι] [DecidableEq ι]
  (e : ι → K)
  (χ : ι → (K →+* ℚ))
  (d : ι → ℕ)
  (T : Type) [CommRing T]
  (b : ι → T)
  -- given
  (he : CompleteOrthogonalIdempotents e)
  (hχe : ∀ a b : ι, χ b (e a) = if b = a then 1 else 0)
  (hsep : ∀ k k' : K, (∀ a, χ a k = χ a k') → k = k')
  (hd : ∀ a, 0 < d a)
  (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n)
  (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹)
  (hb : CompleteOrthogonalIdempotents b)
  (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a) :
  -- imply
  ∃! φ : K →+* T, ∀ a, φ (e a) = b a :=
  ⟨φ hd hval hinv hb hbd, fun c => φ_e hχe hd hval hinv hb hbd c, fun _ hφ' => eq_of_apply_e he hχe hsep hd hval hinv hb hφ' (fun c => φ_e hχe hd hval hinv hb hbd c)⟩


-- created on 2026-10-20
