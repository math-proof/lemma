import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma mem_mapC_of_map_eq_zero {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') {p : Polynomial T} (hp : p.map π = 0) : p ∈ (RingHom.ker π).map (Polynomial.C : T →+* Polynomial T) := by
  rw [Ideal.mem_map_C_iff]
  intro n
  rw [RingHom.mem_ker, ← Polynomial.coeff_map, hp, Polynomial.coeff_zero]

private lemma mul_eq_zero_of_map_eq_zero {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hsq : RingHom.ker π * RingHom.ker π = ⊥) {p q : Polynomial T} (hp : p.map π = 0) (hq : q.map π = 0) : p * q = 0 := by
  have h := Ideal.mul_mem_mul (mem_mapC_of_map_eq_zero π hp) (mem_mapC_of_map_eq_zero π hq)
  rw [← Ideal.map_mul, hsq, Ideal.map_bot] at h
  refine (Submodule.mem_bot _).mp h

private lemma isCoprime_of_map {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π) (hnil : IsNilpotent (RingHom.ker π)) {g k : Polynomial T} (h : IsCoprime (g.map π) (k.map π)) : IsCoprime g k := by
  obtain ⟨u', v', huv⟩ := h
  obtain ⟨u, rfl⟩ := Polynomial.map_surjective π hπ u'
  obtain ⟨v, rfl⟩ := Polynomial.map_surjective π hπ v'
  have he : (u * g + v * k - 1).map π = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, huv, Polynomial.map_one, sub_self]
  have hen : IsNilpotent (u * g + v * k - 1) := by
    rw [Polynomial.isNilpotent_iff]
    intro i
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, ?_⟩
    have hi : (u * g + v * k - 1).coeff i ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, ← Polynomial.coeff_map, he, Polynomial.coeff_zero]
    have hp := Ideal.pow_mem_pow hi n
    rw [hn] at hp
    refine (Submodule.mem_bot _).mp hp
  have hunit : IsUnit (u * g + v * k) := by
    have h1 := hen.isUnit_add_one
    rwa [sub_add_cancel] at h1
  obtain ⟨c, hc⟩ := hunit.exists_left_inv
  exact ⟨c * u, c * v, by rw [mul_assoc, mul_assoc, ← mul_add, hc]⟩

private lemma map_cofactor_eq {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') {f g k : Polynomial T} {g' k' : Polynomial T'} (hg' : g'.Monic) (hfac : f.map π = g' * k') (hg : g.map π = g') (hfk : f = g * k) : k.map π = k' := by
  have h1 : g' * (k.map π - k') = 0 := by
    rw [mul_sub, ← hg, ← Polynomial.map_mul, ← hfk, hfac, hg, sub_self]
  refine sub_eq_zero.mp ((hg'.mul_right_eq_zero_iff).mp h1)

private lemma exists_of_sq {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π) (hsq : RingHom.ker π * RingHom.ker π = ⊥) (f : Polynomial T) (g' k' : Polynomial T') (hg' : g'.Monic) (hcop : IsCoprime g' k') (hfac : f.map π = g' * k') : ∃ g : Polynomial T, g.Monic ∧ g.map π = g' ∧ g ∣ f := by
  obtain ⟨g₀, hg₀, -, hg₀m⟩ := Polynomial.lifts_and_natDegree_eq_and_monic (Polynomial.mem_lifts_of_surjective hπ g') hg'
  obtain ⟨k₀, hk₀⟩ := Polynomial.map_surjective π hπ k'
  obtain ⟨u', v', huv⟩ := hcop
  obtain ⟨u, hu⟩ := Polynomial.map_surjective π hπ u'
  obtain ⟨v, hv⟩ := Polynomial.map_surjective π hπ v'
  have hε : (f - g₀ * k₀).map π = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, hg₀, hk₀, hfac, sub_self]
  have hη : (u * g₀ + v * k₀ - 1).map π = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hu, hv, hg₀, hk₀, huv, Polynomial.map_one, sub_self]
  have hr : (Polynomial.modByMonic (v * (f - g₀ * k₀)) g₀).map π = 0 := by
    rw [Polynomial.map_modByMonic π hg₀m, Polynomial.map_mul, hε, mul_zero, Polynomial.zero_modByMonic]
  have hQ : (Polynomial.divByMonic (v * (f - g₀ * k₀)) g₀).map π = 0 := by
    rw [Polynomial.map_divByMonic π hg₀m, Polynomial.map_mul, hε, mul_zero, Polynomial.zero_divByMonic]
  have hδ₂ : (u * (f - g₀ * k₀) + Polynomial.divByMonic (v * (f - g₀ * k₀)) g₀ * k₀).map π = 0 := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hε, hQ, mul_zero, zero_mul, add_zero]
  have h1 : Polynomial.modByMonic (v * (f - g₀ * k₀)) g₀ + g₀ * (Polynomial.divByMonic (v * (f - g₀ * k₀)) g₀) = v * (f - g₀ * k₀) := Polynomial.modByMonic_add_div _ g₀
  have h2 : (f - g₀ * k₀) * (u * g₀ + v * k₀ - 1) = 0 := mul_eq_zero_of_map_eq_zero π hsq hε hη
  have h3 : (Polynomial.modByMonic (v * (f - g₀ * k₀)) g₀) * (u * (f - g₀ * k₀) + Polynomial.divByMonic (v * (f - g₀ * k₀)) g₀ * k₀) = 0 := mul_eq_zero_of_map_eq_zero π hsq hr hδ₂
  refine ⟨g₀ + Polynomial.modByMonic (v * (f - g₀ * k₀)) g₀, ?_, ?_, ⟨k₀ + (u * (f - g₀ * k₀) + Polynomial.divByMonic (v * (f - g₀ * k₀)) g₀ * k₀), ?_⟩⟩
  ·
    obtain hT | hT := subsingleton_or_nontrivial T
    ·
      let _ : Subsingleton T := hT
      refine Polynomial.monic_of_subsingleton _
    ·
      if hg1 : g₀ = 1 then
        have : Polynomial.modByMonic (v * (f - g₀ * k₀)) g₀ = 0 := by
          rw [hg1]
          refine (Polynomial.modByMonic_eq_zero_iff_dvd Polynomial.monic_one).mpr (one_dvd _)
        rwa [this, add_zero]
      else
        refine hg₀m.add_of_left (Polynomial.degree_lt_degree (Polynomial.natDegree_modByMonic_lt _ hg₀m hg1))
  · rw [Polynomial.map_add, hg₀, hr, add_zero]
  · linear_combination (-k₀) * h1 - h2 - h3

private lemma unique_of_sq {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hsq : RingHom.ker π * RingHom.ker π = ⊥) (f : Polynomial T) (g' k' : Polynomial T') (hg' : g'.Monic) (hcop : IsCoprime g' k') (hfac : f.map π = g' * k') (hπ : Function.Surjective π) (g₁ g₂ : Polynomial T) (h₁ : g₁.Monic ∧ g₁.map π = g' ∧ g₁ ∣ f) (h₂ : g₂.Monic ∧ g₂.map π = g' ∧ g₂ ∣ f) : g₁ = g₂ := by
  obtain ⟨hm₁, hmap₁, ⟨k₁, hk₁⟩⟩ := h₁
  obtain ⟨hm₂, hmap₂, ⟨k₂, hk₂⟩⟩ := h₂
  have hk₁' : k₁.map π = k' := map_cofactor_eq π hg' hfac hmap₁ hk₁
  have hk₂' : k₂.map π = k' := map_cofactor_eq π hg' hfac hmap₂ hk₂
  obtain ⟨u', v', huv⟩ := hcop
  obtain ⟨u, hu⟩ := Polynomial.map_surjective π hπ u'
  obtain ⟨v, hv⟩ := Polynomial.map_surjective π hπ v'
  have hδ : (g₂ - g₁).map π = 0 := by rw [Polynomial.map_sub, hmap₁, hmap₂, sub_self]
  have hη : (k₂ - k₁).map π = 0 := by rw [Polynomial.map_sub, hk₁', hk₂', sub_self]
  have hι : (u * g₁ + v * k₁ - 1).map π = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hu, hv, hmap₁, hk₁', huv, Polynomial.map_one, sub_self]
  have e1 : (g₂ - g₁) * (k₂ - k₁) = 0 := mul_eq_zero_of_map_eq_zero π hsq hδ hη
  have e2 : (g₂ - g₁) * (u * g₁ + v * k₁ - 1) = 0 := mul_eq_zero_of_map_eq_zero π hsq hδ hι
  have e3 : g₂ * k₂ = g₁ * k₁ := by rw [← hk₁, ← hk₂]
  have hdvd : g₁ ∣ (g₂ - g₁) := ⟨u * (g₂ - g₁) - v * (k₂ - k₁), by linear_combination (-1 : Polynomial T) * e2 + v * e3 - v * e1⟩
  by_contra hne
  have hne' : g₂ - g₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  obtain hT' | hT' := subsingleton_or_nontrivial T'
  ·
    have h1 : (1 : T) ∈ RingHom.ker π := by
      rw [RingHom.mem_ker]
      refine Subsingleton.elim _ _
    have h11 := Ideal.mul_mem_mul h1 h1
    rw [hsq, mul_one] at h11
    have h10 : (1 : T) = 0 := (Submodule.mem_bot _).mp h11
    let _ : Subsingleton T := subsingleton_of_zero_eq_one h10.symm
    refine hne' (Subsingleton.elim _ _)
  ·
    have : Nontrivial T := π.domain_nontrivial
    have hd₁ : g₁.natDegree = g'.natDegree := by
      rw [← hmap₁]
      refine (hm₁.natDegree_map π).symm
    have hd₂ : g₂.natDegree = g'.natDegree := by
      rw [← hmap₂]
      refine (hm₂.natDegree_map π).symm
    have hlt : (g₂ - g₁).natDegree < g₁.natDegree := by
      have hdeg : (g₂ - g₁).degree < g₂.degree := Polynomial.degree_sub_lt_left (by rw [Polynomial.degree_eq_natDegree hm₂.ne_zero, Polynomial.degree_eq_natDegree hm₁.ne_zero, hd₁, hd₂]) hm₂.ne_zero (by rw [hm₁.leadingCoeff, hm₂.leadingCoeff])
      have h2 := Polynomial.natDegree_lt_natDegree hne' hdeg
      rwa [hd₂, ← hd₁] at h2
    refine hm₁.not_dvd_of_natDegree_lt hne' hlt hdvd

private lemma helper_main (n : ℕ) : ∀ {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (_ : Function.Surjective π) (_ : RingHom.ker π ^ n = ⊥) (f : Polynomial T) (g' k' : Polynomial T') (_ : g'.Monic) (_ : IsCoprime g' k') (_ : f.map π = g' * k'), ∃! g : Polynomial T, g.Monic ∧ g.map π = g' ∧ g ∣ f := by
  induction n
  ·
    intro T T' _ _ π hπ hn f g' k' hg' hcop hfac
    have h1 : (1 : T) ∈ RingHom.ker π ^ 0 := by
      rw [pow_zero, Ideal.one_eq_top]
      refine Submodule.mem_top
    rw [hn] at h1
    let _ : Subsingleton T := subsingleton_of_zero_eq_one (((Submodule.mem_bot _).mp h1).symm)
    let _ : Subsingleton T' := hπ.subsingleton
    exact ⟨0, ⟨Polynomial.monic_of_subsingleton _, Subsingleton.elim _ _, ⟨0, Subsingleton.elim _ _⟩⟩, fun g _ => Subsingleton.elim _ _⟩
  ·
    rename_i n ih
    intro T T' _ _ π hπ hn f g' k' hg' hcop hfac
    obtain hn0 | hnpos := Nat.eq_zero_or_pos n
    ·
      subst hn0
      have hinj : Function.Injective π := by
        rw [RingHom.injective_iff_ker_eq_bot, ← hn, zero_add, pow_one]
      obtain ⟨g, hg⟩ := Polynomial.map_surjective π hπ g'
      obtain ⟨k, hk⟩ := Polynomial.map_surjective π hπ k'
      refine ⟨g, ⟨Polynomial.monic_of_injective hinj (hg.symm ▸ hg'), hg, ⟨k, ?_⟩⟩, ?_⟩
      ·
        apply Polynomial.map_injective π hinj
        rw [hfac, Polynomial.map_mul, hg, hk]
      ·
        rintro g₂ ⟨-, hg₂, -⟩
        refine Polynomial.map_injective π hinj (by rw [hg₂, hg])
    ·
      have hle : RingHom.ker π ^ n ≤ RingHom.ker π := Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hnpos)
      obtain ⟨π₁, hπ₁mk⟩ : ∃ π₁ : T ⧸ RingHom.ker π ^ n →+* T', π₁.comp (Ideal.Quotient.mk (RingHom.ker π ^ n)) = π := ⟨Ideal.Quotient.lift (RingHom.ker π ^ n) π (fun a ha => hle ha), RingHom.ext fun a => rfl⟩
      have hπ₁ : Function.Surjective π₁ := by
        have h1 : Function.Surjective (π₁.comp (Ideal.Quotient.mk (RingHom.ker π ^ n))) := by
          rw [hπ₁mk]
          refine hπ
        rw [RingHom.coe_comp] at h1
        refine h1.of_comp
      have hk : Ideal.comap (Ideal.Quotient.mk (RingHom.ker π ^ n)) (RingHom.ker π₁) = RingHom.ker π := by
        rw [RingHom.comap_ker, hπ₁mk]
      have hker₁ : RingHom.ker π₁ = (RingHom.ker π).map (Ideal.Quotient.mk (RingHom.ker π ^ n)) := (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm.trans (congrArg (Ideal.map (Ideal.Quotient.mk (RingHom.ker π ^ n))) hk)
      have hker₁n : RingHom.ker π₁ ^ n = ⊥ := by
        rw [hker₁, ← Ideal.map_pow, Ideal.map_quotient_self]
      have hsq : RingHom.ker (Ideal.Quotient.mk (RingHom.ker π ^ n)) * RingHom.ker (Ideal.Quotient.mk (RingHom.ker π ^ n)) = ⊥ := by
        rw [Ideal.mk_ker, ← pow_two, ← pow_mul]
        refine le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
      have hfac₁ : (f.map (Ideal.Quotient.mk (RingHom.ker π ^ n))).map π₁ = g' * k' := by
        rw [Polynomial.map_map, hπ₁mk, hfac]
      obtain ⟨g₁, ⟨hg₁m, hg₁map, hg₁dvd⟩, huniq₁⟩ := ih π₁ hπ₁ hker₁n _ g' k' hg' hcop hfac₁
      obtain ⟨k₁, hk₁⟩ := hg₁dvd
      have hk₁map : k₁.map π₁ = k' := map_cofactor_eq π₁ hg' hfac₁ hg₁map hk₁
      have hnil₁ : RingHom.ker π₁ ^ n = 0 := by
        rw [hker₁n]
        refine Ideal.zero_eq_bot.symm
      have hmaps : IsCoprime (g₁.map π₁) (k₁.map π₁) := by
        rw [hg₁map, hk₁map]
        refine hcop
      have hcop₁ : IsCoprime g₁ k₁ := isCoprime_of_map π₁ hπ₁ ⟨n, hnil₁⟩ hmaps
      obtain ⟨g, hgm, hgmap, hgdvd⟩ := exists_of_sq (Ideal.Quotient.mk (RingHom.ker π ^ n)) Ideal.Quotient.mk_surjective hsq f g₁ k₁ hg₁m hcop₁ hk₁
      refine ⟨g, ⟨hgm, by rw [← hπ₁mk, ← Polynomial.map_map, hgmap, hg₁map], hgdvd⟩, ?_⟩
      rintro h ⟨hhm, hhmap, hhdvd⟩
      have hh₁ : h.map (Ideal.Quotient.mk (RingHom.ker π ^ n)) = g₁ := huniq₁ _ ⟨hhm.map _, by rw [Polynomial.map_map, hπ₁mk, hhmap], Polynomial.map_dvd _ hhdvd⟩
      refine (unique_of_sq (Ideal.Quotient.mk (RingHom.ker π ^ n)) hsq f g₁ k₁ hg₁m hcop₁ hk₁ Ideal.Quotient.mk_surjective g h ⟨hgm, hgmap, hgdvd⟩ ⟨hhm, hh₁, hhdvd⟩).symm

/--
[Polynomial_existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot.lean)
-/
@[path]
private lemma main
  {T T' : Type u} [CommRing T] [CommRing T']
  (π : T →+* T')
  (f : Polynomial T)
  (g' k' : Polynomial T')
  -- given
  (hπ : Function.Surjective π)
  (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
  (hg' : g'.Monic)
  (hcop : IsCoprime g' k')
  (hfac : f.map π = g' * k') :
  -- imply
  ∃! g : Polynomial T, g.Monic ∧ g.map π = g' ∧ g ∣ f := by
  -- proof
  obtain ⟨n, hn⟩ := hnil
  refine helper_main n π hπ hn f g' k' hg' hcop hfac


-- created on 2026-10-20
