import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[IsLocalRing_eq_and_exists_isUnit_and_eq_mul_of_mul_eq_pow_of_span_pair_isPrime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_eq_and_exists_isUnit_and_eq_mul_of_mul_eq_pow_of_span_pair_isPrime.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {p U V X Y w : R}
  {E E₀ : ℕ}
  -- given
  (hE : 1 ≤ E)
  (hE₀ : 1 ≤ E₀)
  (hUV : U * V = p ^ E)
  (hP : (Ideal.span {p, U}).IsPrime)
  (hP' : (Ideal.span {p, V}).IsPrime)
  (hUP' : U ∉ Ideal.span {p, V})
  (hVP : V ∉ Ideal.span {p, U})
  (hw : IsUnit w)
  (hXY : X * Y = p ^ E₀ * w)
  (hX : ∃ γ, IsUnit γ ∧ X - γ * U ∈ Ideal.span {p, V})
  (hY : ∃ γ, IsUnit γ ∧ Y - γ * V ∈ Ideal.span {p, U}) :
  -- imply
  E₀ = E ∧ ∃ a b : R, IsUnit a ∧ IsUnit b ∧ X = U * a ∧ Y = V * b := by
  -- proof
  obtain ⟨γ, hγ, hXγ⟩ := hX
  obtain ⟨γ', hγ', hYγ⟩ := hY
  have hpP : p ∈ Ideal.span {p, U} := Ideal.subset_span (Set.mem_insert _ _)
  have hUP : U ∈ Ideal.span {p, U} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hpP' : p ∈ Ideal.span {p, V} := Ideal.subset_span (Set.mem_insert _ _)
  have hVP' : V ∈ Ideal.span {p, V} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hp0 : p ≠ 0 := by
    intro hp
    have h0 : U * V = 0 := by
      rw [hUV, hp, zero_pow (by omega)]
    obtain h | h := mul_eq_zero.mp h0
    ·
      apply hUP'
      rw [h]
      apply zero_mem
    ·
      apply hVP
      rw [h]
      apply zero_mem
  have hpu : ¬ IsUnit p := fun h => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hpP h)
  have hpm : p ∈ maximalIdeal R := (mem_maximalIdeal p).mpr hpu
  have hUm : U ∈ maximalIdeal R := le_maximalIdeal hP.ne_top hUP
  have hVm : V ∈ maximalIdeal R := le_maximalIdeal hP'.ne_top hVP'
  have hpsp : p ∈ Ideal.span {p} := Ideal.mem_span_singleton_self p
  have hmeet : ∀ t, t ∈ Ideal.span {p, U} → t ∈ Ideal.span {p, V} → ∃ z, t = p * z := by
    intro t ht ht'
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp ht
    have hbU : b * U ∈ Ideal.span {p, V} := by
      have h1 : a * p + b * U - a * p ∈ Ideal.span {p, V} := sub_mem ht' (Ideal.mul_mem_left _ _ hpP')
      rwa [add_sub_cancel_left] at h1
    have hb : b ∈ Ideal.span {p, V} := (hP'.mem_or_mem hbU).resolve_right hUP'
    obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.mp hb
    refine ⟨a + c * U + d * p ^ (E - 1), ?_⟩
    have hE' : p ^ E = p * p ^ (E - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    calc
      _ = a * p + c * p * U + d * (U * V) := by ring
      _ = p * (a + c * U + d * p ^ (E - 1)) := by
        rw [hUV, hE']
        ring
  have hunit : ∀ {a m : R}, IsUnit a → m ∈ maximalIdeal R → IsUnit (a + m) := by
    intro a m ha hm
    by_contra h
    have h1 : a + m ∈ maximalIdeal R := (mem_maximalIdeal _).mpr h
    apply (mem_maximalIdeal _).mp _ ha
    have h3 := sub_mem h1 hm
    rwa [add_sub_cancel_right] at h3
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ min E E₀ → ∃ a b s t : R, IsUnit a ∧ IsUnit b ∧ X = U * a + p ^ k * s ∧ Y = V * b + p ^ k * t := by
    intro k hk hkm
    induction k
    ·
      apply absurd hk
      omega
    ·
      rename_i k ih
      obtain hk0 | hkpos := Nat.eq_zero_or_pos k
      ·
        subst hk0
        have hpE₀ : p ^ E₀ ∈ Ideal.span {p} := Ideal.pow_mem_of_mem _ hpsp _ hE₀
        have hXYU : X * Y ∈ Ideal.span {p, U} := by
          rw [hXY]
          apply Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpP _ hE₀)
        have hXYV : X * Y ∈ Ideal.span {p, V} := by
          rw [hXY]
          apply Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpP' _ hE₀)
        have hYnot : Y ∉ Ideal.span {p, U} := by
          intro hYm
          have h1 : γ' * V ∈ Ideal.span {p, U} := by
            have h2 := sub_mem hYm hYγ
            rwa [sub_sub_cancel] at h2
          obtain h | h := hP.mem_or_mem h1
          · apply hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h hγ')
          · apply hVP h
        have hXnot : X ∉ Ideal.span {p, V} := by
          intro hXm
          have h1 : γ * U ∈ Ideal.span {p, V} := by
            have h2 := sub_mem hXm hXγ
            rwa [sub_sub_cancel] at h2
          obtain h | h := hP'.mem_or_mem h1
          · apply hP'.ne_top (Ideal.eq_top_of_isUnit_mem _ h hγ)
          · apply hUP' h
        have hXmem : X ∈ Ideal.span {p, U} := (hP.mem_or_mem hXYU).resolve_right hYnot
        have hYmem : Y ∈ Ideal.span {p, V} := (hP'.mem_or_mem hXYV).resolve_left hXnot
        obtain ⟨s, hs⟩ := hmeet _ (sub_mem hXmem (Ideal.mul_mem_left _ _ hUP)) hXγ
        obtain ⟨t, ht⟩ := hmeet _ hYγ (sub_mem hYmem (Ideal.mul_mem_left _ _ hVP'))
        refine ⟨γ, γ', s, t, hγ, hγ', ?_, ?_⟩
        ·
          rw [zero_add, pow_one]
          linear_combination hs
        ·
          rw [zero_add, pow_one]
          linear_combination ht
      ·
        obtain ⟨a, b, s, t, ha, hb, hXe, hYe⟩ := ih hkpos (by omega)
        have hkE : k < E := by omega
        have hkE₀ : k < E₀ := by omega
        have hE1 : p ^ E₀ = p ^ k * p ^ (E₀ - k) := by
          rw [← pow_add]
          congr 1
          omega
        have hE2 : p ^ E = p ^ k * p ^ (E - k) := by
          rw [← pow_add]
          congr 1
          omega
        have h3 : p ^ k * (a * t * U + b * s * V + p ^ k * (s * t)) = p ^ E₀ * w - p ^ E * (a * b) := by
          rw [← hXY, ← hUV, hXe, hYe]
          ring
        have hexp : p ^ k * (a * t * U + b * s * V + p ^ k * (s * t)) = p ^ k * (p ^ (E₀ - k) * w - p ^ (E - k) * (a * b)) := by
          rw [h3, hE1, hE2]
          ring
        have hcancel := mul_left_cancel₀ (pow_ne_zero _ hp0) hexp
        have hsum : a * t * U + b * s * V ∈ Ideal.span {p} := by
          have h4 : a * t * U + b * s * V = (p ^ (E₀ - k) * w - p ^ (E - k) * (a * b)) - p ^ k * (s * t) := by
            rw [← hcancel]
            ring
          rw [h4]
          refine sub_mem (sub_mem ?_ ?_) ?_
          · apply Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpsp _ (by omega))
          · apply Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpsp _ (by omega))
          · apply Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpsp _ hkpos)
        have hle1 : Ideal.span {p} ≤ Ideal.span {p, V} := Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
        have hle2 : Ideal.span {p} ≤ Ideal.span {p, U} := Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
        have htmem : t ∈ Ideal.span {p, V} := by
          have h4 : a * t * U ∈ Ideal.span {p, V} := by
            have h5 := sub_mem (hle1 hsum) (Ideal.mul_mem_left _ (b * s) hVP')
            rwa [add_sub_cancel_right] at h5
          obtain h6 | h6 := hP'.mem_or_mem h4
          ·
            obtain h7 | h7 := hP'.mem_or_mem h6
            · apply absurd (Ideal.eq_top_of_isUnit_mem _ h7 ha) hP'.ne_top
            · apply h7
          · apply absurd h6 hUP'
        have hsmem : s ∈ Ideal.span {p, U} := by
          have h4 : b * s * V ∈ Ideal.span {p, U} := by
            have h5 := sub_mem (hle2 hsum) (Ideal.mul_mem_left _ (a * t) hUP)
            rwa [add_sub_cancel_left] at h5
          obtain h6 | h6 := hP.mem_or_mem h4
          ·
            obtain h7 | h7 := hP.mem_or_mem h6
            · apply absurd (Ideal.eq_top_of_isUnit_mem _ h7 hb) hP.ne_top
            · apply h7
          · apply absurd h6 hVP
        obtain ⟨s₁, s₂, hs12⟩ := Ideal.mem_span_pair.mp hsmem
        obtain ⟨t₁, t₂, ht12⟩ := Ideal.mem_span_pair.mp htmem
        refine ⟨a + p ^ k * s₂, b + p ^ k * t₂, s₁, t₁, ?_, ?_, ?_, ?_⟩
        · apply hunit ha (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpm _ hkpos))
        · apply hunit hb (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpm _ hkpos))
        ·
          rw [hXe, ← hs12]
          ring
        ·
          rw [hYe, ← ht12]
          ring
  obtain ⟨a, b, s, t, ha, hb, hXe, hYe⟩ := key (min E E₀) (le_min hE hE₀) le_rfl
  have hexp : p ^ min E E₀ * (a * t * U + b * s * V + p ^ min E E₀ * (s * t)) + p ^ E * (a * b) = p ^ E₀ * w := by
    rw [← hXY, ← hUV, hXe, hYe]
    ring
  obtain hlt | heq | hgt := lt_trichotomy E₀ E
  ·
    exfalso
    have hm : min E E₀ = E₀ := min_eq_right hlt.le
    rw [hm] at hexp
    have hpowE : p ^ E = p ^ E₀ * p ^ (E - E₀) := by
      rw [← pow_add]
      congr 1
      omega
    have h1 : p ^ E₀ * (a * t * U + b * s * V + p ^ E₀ * (s * t) + p ^ (E - E₀) * (a * b)) = p ^ E₀ * w := by
      rw [← hexp, hpowE]
      ring
    have hw' := mul_left_cancel₀ (pow_ne_zero _ hp0) h1
    refine (mem_maximalIdeal _).mp ?_ hw
    rw [← hw']
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · apply Ideal.mul_mem_left _ _ hUm
    · apply Ideal.mul_mem_left _ _ hVm
    · apply Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpm _ hE₀)
    · apply Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpm _ (by omega))
  ·
    refine ⟨heq, a + V * s, b + U * t, ?_, ?_, ?_, ?_⟩
    · apply hunit ha (Ideal.mul_mem_right _ _ hVm)
    · apply hunit hb (Ideal.mul_mem_right _ _ hUm)
    ·
      rw [hXe, show min E E₀ = E by rw [heq, min_self], ← hUV]
      ring
    ·
      rw [hYe, show min E E₀ = E by rw [heq, min_self], ← hUV]
      ring
  ·
    exfalso
    have hm : min E E₀ = E := min_eq_left hgt.le
    rw [hm] at hexp
    have hpow : p ^ E * p ^ (E₀ - E) = p ^ E₀ := by
      rw [← pow_add]
      congr 1
      omega
    have h1 : p ^ E * (a * b + (a * t * U + b * s * V + p ^ E * (s * t))) = p ^ E * (p ^ (E₀ - E) * w) := calc
      _ = p ^ E * (a * t * U + b * s * V + p ^ E * (s * t)) + p ^ E * (a * b) := by ring
      _ = p ^ E₀ * w := hexp
      _ = p ^ E * (p ^ (E₀ - E) * w) := by rw [← mul_assoc, hpow]
    have h2 := mul_left_cancel₀ (pow_ne_zero _ hp0) h1
    apply (mem_maximalIdeal _).mp _ (ha.mul hb)
    have h3 : a * b = p ^ (E₀ - E) * w - (a * t * U + b * s * V + p ^ E * (s * t)) := by
      rw [← h2]
      ring
    rw [h3]
    refine sub_mem ?_ (add_mem (add_mem ?_ ?_) ?_)
    · apply Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpm _ (by omega))
    · apply Ideal.mul_mem_left _ _ hUm
    · apply Ideal.mul_mem_left _ _ hVm
    · apply Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpm _ hE)


-- created on 2026-10-20
