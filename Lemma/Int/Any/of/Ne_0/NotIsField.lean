import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing


private lemma eq_bot_of_height_eq_zero {R : Type u} [CommRing R] [IsDomain R] {q : Ideal R} [q.IsPrime]
  (h : q.height = 0) : q = ⊥ := by
  rw [Ideal.height_eq_zero_iff] at h
  exact le_bot_iff.mp (h.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le)

private lemma exists_isPrime_ne_bot_ne_maximalIdeal_not_mem
  {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (h2 : ¬ (maximalIdeal R).height ≤ 1) (s : R) (hs : s ≠ 0) :
  ∃ p : Ideal R, p.IsPrime ∧ p ≠ ⊥ ∧ p ≠ maximalIdeal R ∧ s ∉ p := by
  classical
  by_contra H
  apply h2
  have H' : ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≠ maximalIdeal R → s ∈ p := by
    intro p hp hb hm
    by_contra hsp
    exact H ⟨p, hp, hb, hm, hsp⟩
  if hsu : IsUnit s then
    refine (Ideal.height_le_iff (n := 1)).mpr fun q hq hqm => ?_
    have hqb : q = ⊥ := by
      by_contra hqb
      have hone : (1 : R) ∈ q := by
        obtain ⟨u, rfl⟩ := hsu
        have := H' q hq hqb hqm.ne
        simpa using q.mul_mem_right (↑u⁻¹ : R) this
      refine hq.ne_top ((Ideal.eq_top_iff_one q).mpr hone)
    subst hqb
    rw [Ideal.height_bot]
    apply zero_lt_one
  else
    have hsm : s ∈ maximalIdeal R := (mem_maximalIdeal s).mpr hsu
    have hstop : Ideal.span {s} ≠ ⊤ := by
      rwa [Ne, Ideal.span_singleton_eq_top]
    have key : ∀ x ∈ maximalIdeal R, x ∈ ⋃ p ∈ (Ideal.span {s}).minimalPrimes, (p : Set R) := by
      intro x hx
      if hx0 : x = 0 then
        obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hstop
        apply Set.mem_biUnion hp (by rw [hx0]; apply p.zero_mem)
      else
        obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (I := Ideal.span {x})
          (by rw [Ne, Ideal.span_singleton_eq_top]; exact (mem_maximalIdeal x).mp hx)
        have hpP : p.IsPrime := hp.1.1
        have hxp : x ∈ p := hp.1.2 (Ideal.subset_span rfl)
        have hp1 : p.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp
        have hpb : p ≠ ⊥ := fun h => hx0 (by rwa [h] at hxp)
        have hpm : p ≠ maximalIdeal R := fun h => h2 (h ▸ hp1)
        have hsp : s ∈ p := H' p hpP hpb hpm
        have hpmin : p ∈ (Ideal.span {s}).minimalPrimes := by
          refine ⟨⟨hpP, (Ideal.span_singleton_le_iff_mem _).mpr hsp⟩, fun q ⟨hq, hsq⟩ hqp => ?_⟩
          by_contra hne
          have hlt : q < p := lt_of_le_of_ne hqp (fun h => hne (h ▸ le_rfl))
          have hqb : q ≠ ⊥ := fun h => hs (by have := hsq (Ideal.subset_span rfl); rwa [h] at this)
          have := hq
          have h1 : (1 : ENat) ≤ q.height := by
            rw [ENat.one_le_iff_ne_zero]
            exact fun h0 => hqb (eq_bot_of_height_eq_zero h0)
          have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
          have h4 : (2 : ENat) ≤ p.height := calc
            _ = 1 + 1 := by norm_num
            _ ≤ q.height + 1 := by gcongr
            _ ≤ p.height := h3
          refine absurd (h4.trans hp1) (by norm_num)
        refine Set.mem_biUnion hpmin hxp
    have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (I := Ideal.span {s})
    obtain ⟨p₀, hp₀⟩ := Ideal.nonempty_minimalPrimes hstop
    have hsub : ((maximalIdeal R : Set R)) ⊆
      ⋃ (i : Ideal R) (_ : i ∈ (↑hfin.toFinset : Set (Ideal R))), ((id i : Ideal R) : Set R) := by
      intro x hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (key x hx)
      exact Set.mem_iUnion₂.mpr ⟨p, hfin.mem_toFinset.mpr hp, hxp⟩
    obtain ⟨p, hpF, hmp⟩ :=
      (Ideal.subset_union_prime p₀ p₀ (fun p hp _ _ => (hfin.mem_toFinset.mp hp).1.1)).mp hsub
    have hp := hfin.mem_toFinset.mp hpF
    have hpm : p = maximalIdeal R := ((maximalIdeal.isMaximal R).eq_of_le hp.1.1.ne_top hmp).symm
    subst hpm
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp
/--
[IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  {s : R}
-- given
  (hR : ¬ IsField R)
  (hs : s ≠ 0) :
-- imply
  ∃ q : Ideal R, q.IsPrime ∧ s ∉ q ∧ ringKrullDim (R ⧸ q) = 1 := by
-- proof
  classical
    have hm0 : maximalIdeal R ≠ ⊥ := fun h => hR (isField_iff_maximalIdeal_eq.mpr h)
    let S : Set (Ideal R) := {q | q.IsPrime ∧ s ∉ q ∧ q ≠ maximalIdeal R}
    have h0S : (⊥ : Ideal R) ∈ S := ⟨Ideal.isPrime_bot, by simpa [Ideal.mem_bot] using hs, hm0.symm⟩
    obtain ⟨q, ⟨hqP, hsq, hqm⟩, hqmax⟩ := set_has_maximal_iff_noetherian.mpr inferInstance S ⟨⊥, h0S⟩
    refine ⟨q, hqP, hsq, ?_⟩
    have := hqP
    have : Nontrivial (R ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hqP.ne_top
    have : IsLocalRing (R ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
    have hs' : Ideal.Quotient.mk q s ≠ 0 := fun h => hsq (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hle : (maximalIdeal (R ⧸ q)).height ≤ 1 := by
      by_contra h2
      obtain ⟨pbar, hpbar, hpb, hpm, hsp⟩ :=
        exists_isPrime_ne_bot_ne_maximalIdeal_not_mem h2 _ hs'
      let p : Ideal R := pbar.comap (Ideal.Quotient.mk q)
      have hpP : p.IsPrime := Ideal.IsPrime.comap _
      have hqp : q ≤ p := fun x hx => by
        show Ideal.Quotient.mk q x ∈ pbar
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; apply pbar.zero_mem
      have hmap : pbar = p.map (Ideal.Quotient.mk q) := (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm
      have hqp' : q ≠ p := fun h => hpb (by rw [hmap, ← h, Ideal.map_quotient_self])
      have hsp' : s ∉ p := hsp
      have hpm' : p ≠ maximalIdeal R := by
        intro h
        apply hpm
        have hmax : p.IsMaximal := h ▸ maximalIdeal.isMaximal R
        obtain htop | hmax' := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective (I := p) hmax
        · exact absurd (hmap.trans htop) hpbar.ne_top
        · exact IsLocalRing.eq_maximalIdeal (hmap ▸ hmax')
      refine hqmax p ⟨hpP, hsp', hpm'⟩ (lt_of_le_of_ne hqp hqp')
    have hne : (maximalIdeal (R ⧸ q)).height ≠ 0 := by
      intro h0
      have hmb : maximalIdeal (R ⧸ q) = ⊥ := eq_bot_of_height_eq_zero h0
      have hF : IsField (R ⧸ q) := isField_iff_maximalIdeal_eq.mpr hmb
      refine hqm (IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField q hF))
    have h1 : (maximalIdeal (R ⧸ q)).height = 1 := le_antisymm hle (ENat.one_le_iff_ne_zero.mpr hne)
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h1]
    rfl


-- created on 2026-10-23
