import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.BurnsidePaqbReduction
import Lemma.Nat.MulCardConjClassCard_StabilizerConjActG.eq.CardG
import Lemma.Nat.ConjClass.of.IsConj
import sympy.atlas.GroupTheory.BurnsidePaqb.ClassSum


namespace BurnsidePaqb

/--
[eq_prime_pow_mul_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SolvableInduction.lean)
-/
@[path]
private lemma eq_prime_pow_mul_of_dvd
  {G : Type u} [Group G] [Fintype G]
  {p q a b d : ℕ}
-- given
  (hp : p.Prime)
  (hq : q.Prime)
  (hdvd : d ∣ p ^ a * q ^ b) :
-- imply
  ∃ a' b', d = p ^ a' * q ^ b' := by
-- proof
  classical
  obtain rfl | hd0 := eq_or_ne d 0
  ·
    exfalso
    apply mul_ne_zero (pow_ne_zero a hp.ne_zero) (pow_ne_zero b hq.ne_zero)
    exact zero_dvd_iff.mp hdvd
  ·
    have hsupp : d.factorization.support ⊆ ({p, q} : Finset ℕ) := by
      intro r hr
      rw [Nat.support_factorization] at hr
      have hprime : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hdr : r ∣ d := Nat.dvd_of_mem_primeFactors hr
      have hdiv : r ∣ p ^ a * q ^ b := dvd_trans hdr hdvd
      obtain h | h := hprime.dvd_mul.mp hdiv
      ·
        have hrp : r ∣ p := (Nat.prime_iff.mp hprime).dvd_of_dvd_pow h
        obtain h1 | h1 := (Nat.dvd_prime hp).mp hrp
        · exact absurd h1 hprime.ne_one
        ·
          rw [h1]
          exact Finset.mem_insert_self p {q}
      ·
        have hrq : r ∣ q := (Nat.prime_iff.mp hprime).dvd_of_dvd_pow h
        obtain h1 | h1 := (Nat.dvd_prime hq).mp hrq
        · exact absurd h1 hprime.ne_one
        ·
          rw [h1]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    have hprod := Nat.prod_factorization_pow_eq_self hd0
    rw [← hprod]
    rw [Finsupp.prod_of_support_subset _ hsupp (fun x1 x2 => x1 ^ x2)
      (fun i _ => pow_zero i)]
    if hpq : p = q then
      subst hpq
      refine ⟨d.factorization p, 0, ?_⟩
      have hpair : ({p, p} : Finset ℕ) = {p} := by simp
      rw [hpair, Finset.prod_singleton, pow_zero, mul_one]
    else
      rw [Finset.prod_pair hpq]
      exact ⟨_, _, rfl⟩

end BurnsidePaqb

namespace BurnsidePaqb

/--
[isSolvable_of_prime_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SolvableInduction.lean)
-/
@[path]
private lemma isSolvable_of_prime_card
  {G : Type u} [Group G] [Fintype G]
  {r : ℕ}
-- given
  (hr : r.Prime)
  (hcard : Fintype.card G = r) :
-- imply
  Group.IsSolvable G := by
-- proof
  have : Fact r.Prime := ⟨hr⟩
  have hcyc : IsCyclic G :=
    isCyclic_of_prime_card (by rw [Nat.card_eq_fintype_card, hcard])
  have := hcyc
  let := IsCyclic.commGroup (α := G)
  infer_instance

end BurnsidePaqb


namespace BurnsidePaqb

/--
[exists_ne_one_class_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
private lemma exists_ne_one_class_prime_pow_eq
  [Group G] [Fintype G]
  {p q a b : ℕ}
-- given
  (hp : p.Prime)
  (hq : q.Prime)
  (hcard : Fintype.card G = p ^ a * q ^ b)
  (hb : 1 ≤ b) :
-- imply
  ∃ g : G, g ≠ 1 ∧ ∃ k ≤ a, (conjClass g).card = p ^ k := by
-- proof
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hqdvd : q ^ b ∣ Nat.card G := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact ⟨p ^ a, by ring⟩
  classical
  obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime q hqdvd
  have : Fintype H := inferInstance
  have hHQ : IsPGroup q H := IsPGroup.of_card hHcard
  have hcardH : 1 < Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, hHcard]
    exact one_lt_pow₀ hq.one_lt (by omega)
  have : Nontrivial H := Fintype.one_lt_card_iff_nontrivial.mp hcardH
  have hnt := IsPGroup.center_nontrivial hHQ
  obtain ⟨gH, hgH⟩ := exists_ne (1 : Subgroup.center H)
  refine ⟨((gH : H) : G), ?_, ?_⟩
  ·
    intro hcon
    exact hgH (Subtype.ext (Subtype.ext hcon))
  ·
    have hle : H ≤ Subgroup.centralizer {((gH : H) : G)} := by
      intro h hh
      rw [Subgroup.mem_centralizer_iff]
      simp only [Set.mem_singleton_iff, forall_eq]
      have hmem := Subgroup.mem_center_iff.mp gH.property ⟨h, hh⟩
      have hcoe := congrArg (fun x : H => (x : G)) hmem
      rwa [Subgroup.coe_mul, Subgroup.coe_mul, eq_comm] at hcoe
    set g : G := ((gH : H) : G) with hg
    have hdvd : q ^ b ∣ Fintype.card (Subgroup.centralizer {g}) := by
      have h1 : Nat.card H ∣ Nat.card (Subgroup.centralizer {g}) :=
        Subgroup.card_dvd_of_le hle
      rw [hHcard] at h1
      rwa [Nat.card_eq_fintype_card] at h1
    have hclass := conjClass_card_mul_centralizer_card (g := g)
    rw [hcard] at hclass
    obtain ⟨t, ht⟩ := hdvd
    refine (Nat.dvd_prime_pow hp).mp ⟨t, ?_⟩
    refine (mul_right_cancel₀ (pow_ne_zero b hq.ne_zero) ?_).symm
    calc
      _ = (conjClass g).card * (q ^ b * t) := by ring
      _ = (conjClass g).card * Fintype.card (Subgroup.centralizer {g}) := by rw [ht]
      _ = p ^ a * q ^ b := hclass


end BurnsidePaqb

namespace BurnsidePaqb

/--
[burnside_paqb_of_simple_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SolvableInduction.lean)
-/
@[path]
private lemma burnside_paqb_of_simple_prime
  {G : Type u} [Group G] [Fintype G]
  {p q a b : ℕ}
-- given
  (C6 : ∀ {H : Type u} [Group H] [Fintype H], IsSimpleGroup H → (∃ g : H, g ≠ 1 ∧ IsPrimePow (conjClass g).card) → ∃ r : ℕ, r.Prime ∧ Fintype.card H = r)
  (hp : Nat.Prime p)
  (hq : Nat.Prime q)
  (hcard : Fintype.card G = p ^ a * q ^ b) :
-- imply
  Group.IsSolvable G := by
-- proof
  classical
  suffices h : ∀ n : ℕ, ∀ (H : Type u) [Group H] [Fintype H],
    Fintype.card H = n →
    (∃ a' b', Fintype.card H = p ^ a' * q ^ b') →
    Group.IsSolvable H by
    exact h _ G hcard ⟨a, b, hcard⟩
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih H _ _ hcardH hform
  obtain ⟨a', b', hform'⟩ := hform
  by_cases htriv : Fintype.card H = 1
  ·
    have : Subsingleton H :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq htriv)
    infer_instance
  ·
    have hpos1 : 1 < Fintype.card H := by
      have hpos := Fintype.card_pos (α := H)
      omega
    have : Nontrivial H :=
      Fintype.one_lt_card_iff_nontrivial.mp hpos1
    by_cases hnorm : ∃ N : Subgroup H, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤
    · obtain ⟨N, hNnorm, hNbot, hNtop⟩ := hnorm
      have := hNnorm
      have hE : Fintype.card H
        = Fintype.card (H ⧸ N) * Fintype.card N := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
        rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
          Nat.card_eq_fintype_card] at h
      have hdvdN : Fintype.card N ∣ Fintype.card H := by
        have h := Subgroup.card_subgroup_dvd_card N
        rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
      have hNlt : Fintype.card N < Fintype.card H := by
        have hne : Fintype.card N ≠ Fintype.card H := by
          intro hcon
          apply hNtop
          have h' : Nat.card N = Nat.card H := by
            rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          exact Subgroup.eq_top_of_card_eq N h'
        have hle := Nat.le_of_dvd Fintype.card_pos hdvdN
        exact lt_of_le_of_ne hle hne
      have hQlt : Fintype.card (H ⧸ N) < Fintype.card H := by
        have hN1 : 1 < Fintype.card N := by
          have hne1 : Fintype.card N ≠ 1 := by
            intro hcon
            apply hNbot
            have h' : Nat.card N = 1 := by
              rwa [Nat.card_eq_fintype_card]
            exact Subgroup.eq_bot_of_card_eq N h'
          have hpos := Fintype.card_pos (α := N)
          omega
        rw [hE]
        exact lt_mul_of_one_lt_right Fintype.card_pos hN1
      have hNform : ∃ a' b', Fintype.card N = p ^ a' * q ^ b' :=
        eq_prime_pow_mul_of_dvd (G := H) hp hq (hform' ▸ hdvdN)
      have hQform : ∃ a' b', Fintype.card (H ⧸ N) = p ^ a' * q ^ b' := by
        refine eq_prime_pow_mul_of_dvd (G := H) (a := a') (b := b') hp hq ?_
        have hdvdQ : Fintype.card (H ⧸ N) ∣ Fintype.card H := by
          rw [hE]
          exact dvd_mul_right _ _
        exact hform' ▸ hdvdQ
      have hNlt' : Fintype.card N < n := by
        rw [← hcardH]; exact hNlt
      have hQlt' : Fintype.card (H ⧸ N) < n := by
        rw [← hcardH]; exact hQlt
      have hNsol : Group.IsSolvable N := ih _ hNlt' N rfl hNform
      have hQsol : Group.IsSolvable (H ⧸ N) := ih _ hQlt' (H ⧸ N) rfl hQform
      exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨hNsol, hQsol⟩
    · push Not at hnorm
      have : IsSimpleGroup H :=
        { toNontrivial := inferInstance,
          eq_bot_or_eq_top_of_normal := fun N hN => by
            by_cases h : N = ⊥
            · exact Or.inl h
            · exact Or.inr (hnorm N hN h) }
      have hab : 1 ≤ a' ∨ 1 ≤ b' := by
        by_contra hcon
        push Not at hcon
        have ha0 : a' = 0 := by omega
        have hb0 : b' = 0 := by omega
        rw [ha0, hb0] at hform'
        simp at hform'
        omega
      obtain ⟨g, hg1, rr, hrr, kk, hclass⟩ :
        ∃ (g : H) (_ : g ≠ 1) (rr : ℕ) (_ : rr.Prime) (kk : ℕ),
          (conjClass g).card = rr ^ kk := by
        obtain ha | hb := hab
        ·
          have hcard' : Fintype.card H = q ^ b' * p ^ a' := by
            rw [hform']; ring
          obtain ⟨g, hg1, hex⟩ := exists_ne_one_class_prime_pow_eq hq hp hcard' ha
          obtain ⟨k, hk, hcl⟩ := hex
          exact ⟨g, hg1, q, hq, k, hcl⟩
        ·
          obtain ⟨g, hg1, hex⟩ := exists_ne_one_class_prime_pow_eq hp hq hform' hb
          obtain ⟨k, hk, hcl⟩ := hex
          exact ⟨g, hg1, p, hp, k, hcl⟩
      by_cases hk0 : kk = 0
      · subst hk0
        rw [pow_zero] at hclass
        have hgmem : g ∈ conjClass g :=
          mem_conjClass_iff.mpr (IsConj.refl g)
        have hconj : ∀ h : H, h * g * h⁻¹ = g := by
          intro h
          have hmem : h * g * h⁻¹ ∈ conjClass g :=
            conj_mem_conjClass g h g hgmem
          have hcard1 := hclass
          obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
          rw [hx] at hmem
          have hxg : x = g := by
            have hgx : g ∈ ({x} : Finset H) := by rw [← hx]; exact hgmem
            exact (Finset.mem_singleton.mp hgx).symm
          have hmemx := Finset.mem_singleton.mp hmem
          rw [hmemx, hxg]
        have hcenter : g ∈ Subgroup.center H := by
          rw [Subgroup.mem_center_iff]
          intro h
          have hc := hconj h
          have heq : h * g * h⁻¹ * h = g * h := by rw [hc]
          rwa [mul_assoc, inv_mul_cancel, mul_one] at heq
        have hcenterBot : Subgroup.center H ≠ ⊥ := by
          intro hcon
          apply hg1
          have hmem : g ∈ (⊥ : Subgroup H) := hcon ▸ hcenter
          exact Subgroup.mem_bot.mp hmem
        have hcenterTop :=
          (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_left
            hcenterBot
        have hcomm : ∀ x y : H, x * y = y * x := by
          intro x y
          have hx : x ∈ Subgroup.center H := hcenterTop ▸ Subgroup.mem_top x
          exact (Subgroup.mem_center_iff.mp hx y).symm
        let grp : Group H := inferInstance
        let : CommGroup H := { toGroup := grp, mul_comm := hcomm }
        have hr : (Fintype.card H).Prime := by
          simpa only [Nat.card_eq_fintype_card] using
            (IsSimpleGroup.prime_card (α := H))
        exact isSolvable_of_prime_card hr rfl
      ·
        have hpp : IsPrimePow (conjClass g).card := by
          rw [hclass]
          exact hrr.isPrimePow.pow hk0
        obtain ⟨r, hr, hrcard⟩ := C6 inferInstance ⟨g, hg1, hpp⟩
        exact isSolvable_of_prime_card hr hrcard

end BurnsidePaqb


-- created on 2026-10-20
-- updated on 2026-10-24
