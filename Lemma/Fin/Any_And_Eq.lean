import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma Finsupp.exists_eq_sum_single_of_mapDomain_eq_sum_single'
  {α β : Type}
  {f : α → β}
  {E : Finsupp α ℤ}
  {d : ℕ}
  {v : Fin d → β}
  -- given
  (hE : 0 ≤ E)
  (hv : Function.Injective v)
  (h : Finsupp.mapDomain f E = ∑ i, Finsupp.single (v i) (1 : ℤ)) :
  -- imply
  ∃ Q : Fin d → α, E = ∑ i, Finsupp.single (Q i) (1 : ℤ) ∧ ∀ i, f (Q i) = v i := by
  -- proof
  classical
  have hmass : ∀ (D : Finsupp α ℤ), (Finsupp.mapDomain f D).sum (fun _ n => n) = D.sum (fun _ n => n) := fun D => Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
  have htarget : ∀ b, (∑ i, Finsupp.single (v i) (1 : ℤ)) b = if ∃ i, v i = b then 1 else 0 := by
    intro b
    rw [Finsupp.finset_sum_apply]
    split_ifs with hb
    ·
      obtain ⟨i, rfl⟩ := hb
      rw [Finset.sum_eq_single i]
      · simp
      ·
        intro j _ hj
        rw [Finsupp.single_apply, if_neg (fun h => hj (hv h))]
      · simp
    ·
      push Not at hb
      apply Finset.sum_eq_zero fun i _ => by rw [Finsupp.single_apply, if_neg (hb i)]
  have hfib : ∀ i, ∃ a, f a = v i ∧ 0 < E a := by
    intro i
    by_contra hcon
    push Not at hcon
    have h1 : (Finsupp.mapDomain f E) (v i) = 1 := by
      rw [h, htarget, if_pos ⟨i, rfl⟩]
    have h0 : (Finsupp.mapDomain f E) (v i) ≤ 0 := by
      rw [Finsupp.mapDomain, Finsupp.sum_apply]
      apply Finset.sum_nonpos
      intro a _
      show (Finsupp.single (f a) (E a)) (v i) ≤ 0
      rw [Finsupp.single_apply]
      split_ifs with ha
      · apply hcon a ha
      · apply le_rfl
    omega
  choose Q hQf hQpos using hfib
  have hQinj : Function.Injective Q := fun i j hij => hv (by rw [← hQf i, ← hQf j, hij])
  refine ⟨Q, ?_, hQf⟩
  set E' : Finsupp α ℤ := E - ∑ i, Finsupp.single (Q i) (1 : ℤ) with hE'
  have hsumQ : ∀ a, (∑ i, Finsupp.single (Q i) (1 : ℤ)) a = if ∃ i, Q i = a then 1 else 0 := by
    intro a
    rw [Finsupp.finset_sum_apply]
    split_ifs with ha
    ·
      obtain ⟨i, rfl⟩ := ha
      rw [Finset.sum_eq_single i]
      · simp
      ·
        intro j _ hj
        rw [Finsupp.single_apply, if_neg (fun h => hj (hQinj h))]
      · simp
    ·
      push Not at ha
      apply Finset.sum_eq_zero fun i _ => by rw [Finsupp.single_apply, if_neg (ha i)]
  have hE'nn : 0 ≤ E' := by
    intro a
    simp only [hE', Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply, hsumQ]
    split_ifs with ha
    ·
      obtain ⟨i, rfl⟩ := ha
      have := hQpos i
      omega
    ·
      have := hE a
      simp only [Finsupp.coe_zero, Pi.zero_apply] at this
      omega
  have hmap : Finsupp.mapDomain f E' = 0 := by
    rw [hE', Finsupp.mapDomain_sub, h, Finsupp.mapDomain_finset_sum]
    simp only [Finsupp.mapDomain_single, hQf, sub_self]
  have hzero : E' = 0 := by
    by_contra hne
    obtain ⟨a, ha⟩ : ∃ a, E' a ≠ 0 := by
      by_contra h'
      push Not at h'
      apply hne (Finsupp.ext h')
    have hpos : 0 < E'.sum (fun _ n => n) := by
      rw [Finsupp.sum]
      apply Finset.sum_pos'
      ·
        intro b _
        apply hE'nn b
      · exact ⟨a, Iff.mpr Finsupp.mem_support_iff ha, lt_of_le_of_ne (hE'nn a) (Ne.symm ha)⟩
    rw [← hmass E', hmap, Finsupp.sum_zero_index] at hpos
    apply lt_irrefl _ hpos
  simpa [hE'] using congrArg (· + ∑ i, Finsupp.single (Q i) (1 : ℤ)) hzero

/--
[Finsupp_exists_eq_sum_single_of_mapDomain_eq_sum_single](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Finsupp_exists_eq_sum_single_of_mapDomain_eq_sum_single.lean)
-/
@[path]
private lemma main
  {α β : Type}
  {f : α → β}
  {E : Finsupp α ℤ}
  {d : ℕ}
  {v : Fin d → β}
  -- given
  (hE : 0 ≤ E)
  (hv : Function.Injective v)
  (h : Finsupp.mapDomain f E = ∑ i, Finsupp.single (v i) (1 : ℤ)) :
  -- imply
  ∃ Q : Fin d → α, E = ∑ i, Finsupp.single (Q i) (1 : ℤ) ∧ ∀ i, f (Q i) = v i := by
  -- proof
  apply Finsupp.exists_eq_sum_single_of_mapDomain_eq_sum_single' hE hv h


-- created on 2026-10-20
