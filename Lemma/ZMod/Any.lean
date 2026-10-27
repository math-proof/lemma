import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Finset_exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Finset_exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime.lean)
-/
@[path]
private lemma main
  {q : ℕ} [Fact q.Prime]
  {S : Finset (ℕ × ℕ)}
  -- given
  (hS : S ⊆ Finset.range q ×ˢ Finset.range q)
  (hcard : S.card = q) :
  -- imply
  ∃ a b c d : ℕ, (a, b) ∈ S ∧ c < q ∧ d < q ∧ (c, d) ∉ S ∧ IsUnit (((a * d : ℤ) - (b * c : ℤ) : ℤ) : ZMod q) := by
  -- proof
  classical
  have hq : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hq.two_le
  have cast_inj : ∀ d d' : ℕ, d < q → d' < q → (d : ZMod q) = (d' : ZMod q) → d = d' := by
    intro d d' hd hd' h
    have h' := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd'] at h'
  have cast_ne : ∀ d : ℕ, d < q → d ≠ 0 → (d : ZMod q) ≠ 0 := by
    intro d hd hd0 h
    apply hd0 (cast_inj d 0 hd (by omega) (by rw [h, Nat.cast_zero]))
  obtain ⟨p, hpS, hp0⟩ : ∃ p ∈ S, p ≠ ((0, 0) : ℕ × ℕ) := by
    by_contra hcon
    push Not at hcon
    have hsub : S ⊆ {((0, 0) : ℕ × ℕ)} := fun x hx => Finset.mem_singleton.mpr (hcon x hx)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_singleton, hcard] at hle
    omega
  obtain ⟨a, b⟩ := p
  have hab : (a, b) ∈ Finset.range q ×ˢ Finset.range q := hS hpS
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
  obtain ⟨ha, hb⟩ := hab
  set B : Finset (ℕ × ℕ) := Finset.range q ×ˢ Finset.range q with hB
  set L : Finset (ℕ × ℕ) := B.filter (fun p => (((a * p.2 : ℤ) - (b * p.1 : ℤ) : ℤ) : ZMod q) = 0) with hL
  have hBcard : B.card = q * q := by
    rw [hB, Finset.card_product, Finset.card_range]
  have memL : ∀ c d : ℕ, (c, d) ∈ L ↔ (c < q ∧ d < q) ∧ (a : ZMod q) * d = b * c := by
    intro c d
    simp only [hL, hB, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    push_cast
    rw [sub_eq_zero]
  have hLcard : L.card ≤ q := by
    obtain ha0 | ha0 := Nat.eq_zero_or_pos a
    ·
      have hb0 : b ≠ 0 := by
        intro h
        apply hp0 (by rw [ha0, h])
      have hbq : (b : ZMod q) ≠ 0 := cast_ne b hb hb0
      have first_zero : ∀ c d : ℕ, (c, d) ∈ L → c = 0 := by
        intro c d h
        rw [memL] at h
        obtain ⟨⟨hc, _⟩, h⟩ := h
        rw [ha0, Nat.cast_zero, zero_mul, eq_comm, mul_eq_zero] at h
        obtain h | h := h
        · apply absurd h hbq
        · apply cast_inj c 0 hc (by omega) (by rw [h, Nat.cast_zero])
      calc
        _ ≤ (Finset.range q).card := by
          refine Finset.card_le_card_of_injOn (fun p => p.2) ?_ ?_
          ·
            intro p hp
            obtain ⟨c, d⟩ := p
            apply Iff.mpr Finset.mem_range ((Iff.mp (memL c d) hp).1.2)
          ·
            intro p hcd p' hcd' h
            obtain ⟨c, d⟩ := p
            obtain ⟨c', d'⟩ := p'
            apply Prod.ext ((first_zero c d hcd).trans (first_zero c' d' hcd').symm) h
        _ = q := Finset.card_range q
    ·
      have haq : (a : ZMod q) ≠ 0 := cast_ne a ha (by omega)
      calc
        _ ≤ (Finset.range q).card := by
          refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_
          ·
            intro p hp
            obtain ⟨c, d⟩ := p
            apply Iff.mpr Finset.mem_range ((Iff.mp (memL c d) hp).1.1)
          ·
            intro p hcd p' hcd' h
            obtain ⟨c, d⟩ := p
            obtain ⟨c', d'⟩ := p'
            apply Prod.ext h (cast_inj d d' ((Iff.mp (memL c d) hcd).1.2) ((Iff.mp (memL c' d') hcd').1.2) (mul_left_cancel₀ haq (((Iff.mp (memL c d) hcd).2).trans ((congrArg (fun z : ℕ => (b : ZMod q) * z) h).trans ((Iff.mp (memL c' d') hcd').2).symm))))
        _ = q := Finset.card_range q
  have hmemL : (a, b) ∈ L := Iff.mpr (memL a b) ⟨⟨ha, hb⟩, mul_comm _ _⟩
  have hlt : (S ∪ L).card < B.card := by
    have h1 : (S ∪ L).card + (S ∩ L).card = S.card + L.card := Finset.card_union_add_card_inter S L
    have h2 : 0 < (S ∩ L).card := Iff.mpr Finset.card_pos ⟨(a, b), Iff.mpr Finset.mem_inter ⟨hpS, hmemL⟩⟩
    have hqq : 2 * q ≤ B.card := by
      rw [hBcard]
      apply Nat.mul_le_mul_right q hq2
    omega
  obtain ⟨x, hxB, hxSL⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨c, d⟩ := x
  have hcd : c < q ∧ d < q := by
    simpa only [hB, Finset.mem_product, Finset.mem_range] using hxB
  rw [Finset.mem_union, not_or] at hxSL
  obtain ⟨hxS, hxL⟩ := hxSL
  refine ⟨a, b, c, d, hpS, hcd.1, hcd.2, hxS, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0'
  apply hxL
  rw [memL]
  refine ⟨hcd, ?_⟩
  apply Iff.mp sub_eq_zero _
  have := h0'
  push_cast at this
  apply this


-- created on 2026-10-20
