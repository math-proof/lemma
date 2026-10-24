import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma Ideal.IsHomogeneous.exists_homogeneous_mem_notMem
  [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]
  {I p : Ideal A}
  -- given
  (hI : I.IsHomogeneous 𝒜)
  (h : ¬ I ≤ p) :
  -- imply
  ∃ (n : ℕ) (x : A), x ∈ 𝒜 n ∧ x ∈ I ∧ x ∉ p := by
  -- proof
  classical
  obtain ⟨a, haI, hap⟩ := Iff.mp SetLike.not_le_iff_exists h
  by_contra! H
  apply hap
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  apply Ideal.sum_mem _ fun i _ => H i _ (SetLike.coe_mem _) (hI i haI)

private lemma Ideal.IsHomogeneous.exists_homogeneous_pos_mem_notMem
  [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]
  {I p : Ideal A}
  -- given
  (hI : I.IsHomogeneous 𝒜)
  (hirr : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
  (h : ¬ I ≤ p) :
  -- imply
  ∃ (n : ℕ) (x : A), 0 < n ∧ x ∈ 𝒜 n ∧ x ∈ I ∧ x ∉ p := by
  -- proof
  classical
  obtain ⟨n, x, hxn, hxI, hxp⟩ := hI.exists_homogeneous_mem_notMem h
  refine ⟨n, x, Nat.pos_of_ne_zero ?_, hxn, hxI, hxp⟩
  intro h
  subst h
  apply hxp
  have hx0 : GradedRing.proj 𝒜 0 x = 0 := Iff.mp (HomogeneousIdeal.mem_irrelevant_iff 𝒜 x) (Iff.mp HomogeneousIdeal.mem_iff (hirr hxI))
  rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hxn] at hx0
  rw [hx0]
  apply p.zero_mem

private lemma Ideal.IsHomogeneous.exists_homogeneous_pos_mem_forall_notMem
  [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]
  {I : Ideal A}
  {t : Finset (Ideal A)}
  -- given
  (hI : I.IsHomogeneous 𝒜)
  (hirr : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
  (hprime : ∀ p ∈ t, p.IsPrime)
  (hhom : ∀ p ∈ t, p.IsHomogeneous 𝒜)
  (havoid : ∀ p ∈ t, ¬ I ≤ p) :
  -- imply
  ∃ (n : ℕ) (x : A), 0 < n ∧ x ∈ 𝒜 n ∧ x ∈ I ∧ ∀ p ∈ t, x ∉ p := by
  -- proof
  classical
  suffices H : ∀ t : Finset (Ideal A), (∀ p ∈ t, p.IsPrime) → (∀ p ∈ t, p.IsHomogeneous 𝒜) → (∀ p ∈ t, ¬ I ≤ p) → ∃ (n : ℕ) (x : A), 0 < n ∧ x ∈ 𝒜 n ∧ x ∈ I ∧ ∀ p ∈ t, x ∉ p by
    apply H t hprime hhom havoid
  apply Finset.strongInduction
  intro t ih hprime hhom havoid
  obtain rfl | hne := t.eq_empty_or_nonempty
  · exact ⟨1, 0, Nat.one_pos, zero_mem _, I.zero_mem, by simp⟩
  obtain ⟨p₀, hp₀t, hmin⟩ := t.exists_minimal hne
  have hsub : t.erase p₀ ⊂ t := Finset.erase_ssubset hp₀t
  obtain ⟨n, x, hn, hxn, hxI, hx⟩ := ih _ hsub (fun p hp => hprime p (Finset.mem_of_mem_erase hp)) (fun p hp => hhom p (Finset.mem_of_mem_erase hp)) (fun p hp => havoid p (Finset.mem_of_mem_erase hp))
  if hxp₀ : x ∈ p₀ then
    have hp₀ : p₀.IsPrime := hprime p₀ hp₀t
    obtain ⟨e₀, y₀, he₀, hy₀e, hy₀I, hy₀p⟩ := hI.exists_homogeneous_pos_mem_notMem hirr (havoid p₀ hp₀t)
    have hq : ∀ q ∈ t.erase p₀, ∃ (m : ℕ) (y : A), y ∈ 𝒜 m ∧ y ∈ q ∧ y ∉ p₀ := by
      intro q hq
      obtain ⟨hqne, hqt⟩ := Iff.mp Finset.mem_erase hq
      refine (hhom q hqt).exists_homogeneous_mem_notMem fun hle => ?_
      apply hqne (le_antisymm hle (hmin hqt hle))
    choose! m y hym hyq hyp using hq
    set Y : A := y₀ * ∏ q ∈ t.erase p₀, y q with hYdef
    set e : ℕ := e₀ + ∑ q ∈ t.erase p₀, m q with hedef
    have hYe : Y ∈ 𝒜 e := SetLike.mul_mem_graded hy₀e (SetLike.prod_mem_graded _ _ _ fun q hq => hym q hq)
    have he : 0 < e := Nat.add_pos_left he₀ _
    have hYI : Y ∈ I := I.mul_mem_right _ hy₀I
    have hYp₀ : Y ∉ p₀ := by
      intro hY
      obtain h | h := hp₀.mem_or_mem hY
      · apply hy₀p h
      · apply (Finset.prod_induction (fun q => y q) (· ∉ p₀) (fun a b ha hb hab => (hp₀.mem_or_mem hab).elim ha hb) (fun h1 => hp₀.ne_top (Iff.mpr (Ideal.eq_top_iff_one _) h1)) (fun q hq => hyp q hq)) h
    have hYq : ∀ q ∈ t.erase p₀, Y ∈ q := by
      intro q hq
      rw [hYdef, ← Finset.mul_prod_erase _ _ hq]
      apply q.mul_mem_left _ (q.mul_mem_right _ (hyq q hq))
    refine ⟨n * e, x ^ e + Y ^ n, Nat.mul_pos hn he, ?_, ?_, ?_⟩
    ·
      refine add_mem ?_ ?_
      ·
        have := SetLike.pow_mem_graded e hxn
        rwa [smul_eq_mul, mul_comm] at this
      ·
        have := SetLike.pow_mem_graded n hYe
        rwa [smul_eq_mul] at this
    · apply add_mem (I.pow_mem_of_mem hxI _ he) (I.pow_mem_of_mem hYI _ hn)
    ·
      intro p hp
      obtain rfl | hne' := eq_or_ne p p₀
      ·
        intro hz
        have : Y ^ n ∈ p := by
          have h1 : x ^ e ∈ p := p.pow_mem_of_mem hxp₀ _ he
          simpa using p.sub_mem hz h1
        apply hYp₀ (hp₀.mem_of_pow_mem _ this)
      ·
        have hp' : p ∈ t.erase p₀ := Iff.mpr Finset.mem_erase ⟨hne', hp⟩
        intro hz
        have hpP : p.IsPrime := hprime p hp
        have : x ^ e ∈ p := by
          have h1 : Y ^ n ∈ p := p.pow_mem_of_mem (hYq p hp') _ hn
          simpa using p.sub_mem hz h1
        apply hx p hp' (hpP.mem_of_pow_mem _ this)
  else
    refine ⟨n, x, hn, hxn, hxI, fun p hp => ?_⟩
    obtain rfl | hne' := eq_or_ne p p₀
    · apply hxp₀
    · apply hx p (Iff.mpr Finset.mem_erase ⟨hne', hp⟩)

/--
[HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem.lean)
-/
@[path]
private lemma main
  {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]
  {I : HomogeneousIdeal 𝒜}
  {t : Finset (HomogeneousIdeal 𝒜)}
  -- given
  (hirr : I ≤ HomogeneousIdeal.irrelevant 𝒜)
  (hprime : ∀ p ∈ t, p.toIdeal.IsPrime)
  (havoid : ∀ p ∈ t, ¬ I ≤ p) :
  -- imply
  ∃ (n : ℕ) (x : A), 0 < n ∧ x ∈ 𝒜 n ∧ x ∈ I ∧ ∀ p ∈ t, x ∉ p := by
  -- proof
  classical
  have hprimeI : ∀ p ∈ t.image HomogeneousIdeal.toIdeal, p.IsPrime := by
    simpa using hprime
  have hhomI : ∀ p ∈ t.image HomogeneousIdeal.toIdeal, p.IsHomogeneous 𝒜 := by
    simp
    exact fun p _ => p.isHomogeneous
  have havoidI : ∀ p ∈ t.image HomogeneousIdeal.toIdeal, ¬ I.toIdeal ≤ p := by
    simpa using havoid
  obtain ⟨n, x, hn, hxn, hxI, hx⟩ := I.isHomogeneous.exists_homogeneous_pos_mem_forall_notMem (I := I.toIdeal) (t := t.image HomogeneousIdeal.toIdeal) hirr hprimeI hhomI havoidI
  exact ⟨n, x, hn, hxn, hxI, fun p hp => hx _ (Finset.mem_image_of_mem _ hp)⟩


-- created on 2026-10-20
