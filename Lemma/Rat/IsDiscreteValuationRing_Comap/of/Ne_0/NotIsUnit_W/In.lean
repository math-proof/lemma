import Mathlib
import sympy.Basic
import Lemma.Int.P2MUtil
open IsDiscreteValuationRing
open ValuationSubring


private lemma DC_isDiscreteValuationRing_of_ringHom_of_dvd {R : Type u} {S : Type v} [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (φ : R →+* S) (hinj : Function.Injective φ)
  (hdvd : ∀ a b : R, φ a ∣ φ b → a ∣ b) (t : R) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
  IsDiscreteValuationRing R := by
  classical
  have hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, addVal S (φ x) = n := by
    intro x hx
    have hne : addVal S (φ x) ≠ ⊤ := by
      rw [Ne, addVal_eq_top_iff]
      exact (map_ne_zero_iff φ hinj).mpr hx
    refine ⟨_, (ENat.natCast_toNat hne).symm⟩
  have hunit : ∀ x : R, addVal S (φ x) = 0 → IsUnit x := by
    intro x hx
    apply isUnit_of_dvd_one
    apply hdvd
    rw [map_one, ← addVal_le_iff_dvd, hx]
    apply zero_le
  have hunit' : ∀ x : R, IsUnit x → addVal S (φ x) = 0 := by
    intro x hx
    have h : addVal S (φ x) ≤ addVal S 1 := addVal_le_iff_dvd.mpr (hx.map φ).dvd
    rw [(addVal S).map_one] at h
    exact le_antisymm h zero_le
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ x : R, addVal S (φ x) = n := by
    obtain ⟨n, hn⟩ := hval t ht0
    refine ⟨n, ?_, t, hn⟩
    obtain h | h := Nat.eq_zero_or_pos n
    · exact absurd (hunit t (by rw [hn, h, Nat.cast_zero])) ht
    · exact h
  obtain ⟨d, ⟨hd0, s, hs⟩, hmin⟩ : ∃ d : ℕ, (0 < d ∧ ∃ x : R, addVal S (φ x) = d) ∧
      ∀ m : ℕ, (0 < m ∧ ∃ x : R, addVal S (φ x) = m) → d ≤ m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min' hex hm⟩
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, map_zero, (addVal S).map_zero] at hs
    exact (ENat.top_ne_coe d) hs
  have key : ∀ (a : ℕ) (x : R), addVal S (φ x) = a → ∃ (q : ℕ) (u : Rˣ), x = u * s ^ q := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro x hx
      if ha : a = 0 then
        obtain ⟨u, hu⟩ := hunit x (by rw [hx, ha, Nat.cast_zero])
        exact ⟨0, u, by rw [pow_zero, mul_one, hu]⟩
      else
        have had : d ≤ a := hmin a ⟨Nat.pos_of_ne_zero ha, x, hx⟩
        have hsx : s ∣ x := by
          apply hdvd
          rw [← addVal_le_iff_dvd, hs, hx]
          exact_mod_cast had
        obtain ⟨y, rfl⟩ := hsx
        have hy0 : y ≠ 0 := by
          intro h
          rw [h, mul_zero, map_zero, (addVal S).map_zero] at hx
          exact (ENat.top_ne_coe a) hx
        obtain ⟨n, hn⟩ := hval y hy0
        have hnat : d + n = a := by
          rw [map_mul, (addVal S).map_mul, hs, hn] at hx
          exact_mod_cast hx
        obtain ⟨q, u, rfl⟩ := ih n (by omega) y hn
        exact ⟨q + 1, u, by ring⟩
  have hirr : Irreducible s := by
    refine irreducible_iff.mpr ⟨fun hsu => ?_, fun a b hab => ?_⟩
    ·
      have := hunit' s hsu
      rw [hs] at this
      have : d = 0 := by exact_mod_cast this
      omega
    ·
      have ha0 : a ≠ 0 := by
      intro h; exact hs0 (by rw [hab, h, zero_mul])
      have hb0 : b ≠ 0 := by
        intro h; exact hs0 (by rw [hab, h, mul_zero])
      obtain ⟨na, hna⟩ := hval a ha0
      obtain ⟨nb, hnb⟩ := hval b hb0
      have hsum : na + nb = d := by
        rw [hab, map_mul, (addVal S).map_mul, hna, hnb] at hs
        exact_mod_cast hs
      if hna0 : na = 0 then
        exact Or.inl (hunit a (by rw [hna, hna0, Nat.cast_zero]))
      else
        have := hmin na ⟨Nat.pos_of_ne_zero hna0, a, hna⟩
        exact Or.inr (hunit b (by rw [hnb]; exact_mod_cast (by omega : nb = 0)))
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨s, hirr, ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := hval x hx
  obtain ⟨q, u, hxq⟩ := key n x hn
  exact ⟨q, u, by rw [hxq, mul_comm]⟩

p2m_open "IsDiscreteValuationRing ValuationSubring P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_of_mem_of_not_isUnit.ValuationSubring"
/--
[ValuationSubring_isDiscreteValuationRing_comap_of_mem_of_not_isUnit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_isDiscreteValuationRing_comap_of_mem_of_not_isUnit.lean)
-/
@[path]
private lemma main
  [Field K] [Field F]
  {W : ValuationSubring K} [IsDiscreteValuationRing ↥W]
  {ι : F →+* K}
  {t : F}
-- given
  (ht : ι t ∈ W)
  (ht' : ¬ IsUnit (⟨ι t, ht⟩ : ↥W))
  (ht0 : t ≠ 0) :
-- imply
  IsDiscreteValuationRing ↥(W.comap ι) := by
-- proof
  classical
    have hmem : ∀ x : F, x ∈ W.comap ι ↔ ι x ∈ W := fun x => Iff.rfl
    obtain ⟨φ, hφ⟩ : ∃ φ : ↥(W.comap ι) →+* ↥W, ∀ x : ↥(W.comap ι), (φ x : K) = ι (x : F) :=
      ⟨{ toFun := fun x => ⟨ι (x : F), (hmem x).mp x.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp)
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp) }, fun _ => rfl⟩
    have hιinj : Function.Injective ι := ι.injective
    have hinj : Function.Injective φ := by
      intro a b hab
      have h := congrArg (fun w : ↥W => (w : K)) hab
      simp only [hφ] at h
      exact Subtype.ext (hιinj h)
    have hdvd : ∀ a b : ↥(W.comap ι), φ a ∣ φ b → a ∣ b := by
      intro a b ⟨w, hw⟩
      if ha : a = 0 then
        subst ha
        have hb : (φ b : K) = 0 := by
          rw [hw, map_zero]
          simp
        rw [hφ, map_eq_zero] at hb
        have : b = 0 := Subtype.ext hb
        rw [this]
      else
        have ha' : (a : F) ≠ 0 := fun h => ha (Subtype.ext h)
        have hwK : (w : K) = ι ((b : F) / (a : F)) := by
          have h := congrArg (fun z : ↥W => (z : K)) hw
          have h' : ι (b : F) = ι (a : F) * (w : K) := by simpa [hφ] using h
          rw [map_div₀, h', mul_div_cancel_left₀ _ ((map_ne_zero_iff ι hιinj).mpr ha')]
        have hc : (b : F) / (a : F) ∈ W.comap ι := by
          rw [hmem, ← hwK]
          apply w.2
        refine ⟨⟨(b : F) / (a : F), hc⟩, Subtype.ext ?_⟩
        show (b : F) = (a : F) * ((b : F) / (a : F))
        rw [mul_div_assoc', mul_div_cancel_left₀ _ ha']
    have htmem : t ∈ W.comap ι := (hmem t).mpr ht
    refine DC_isDiscreteValuationRing_of_ringHom_of_dvd φ hinj hdvd ⟨t, htmem⟩
      (fun h => ht0 (congrArg Subtype.val h)) (fun hu => ht' ?_)
    have hφt : φ ⟨t, htmem⟩ = ⟨ι t, ht⟩ := Subtype.ext (hφ _)
    refine hφt ▸ hu.map φ


-- created on 2026-10-23
