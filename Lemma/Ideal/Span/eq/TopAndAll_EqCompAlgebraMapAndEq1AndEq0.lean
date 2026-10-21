import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma eq_one_of_idem_unit
  {R : Type} [CommRing R]
  {e : R}
  -- given
  (he : IsIdempotentElem e)
  (hu : IsUnit e) :
  -- imply
  e = 1 := by
  -- proof
  apply Iff.mp sub_eq_zero (hu.mul_left_cancel (_).trans (mul_zero e).symm)
  rw [mul_sub, mul_one, he.eq, sub_self]

/--
[Ideal_exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one.lean)
-/
@[path]
private lemma main
  {S : Type} [CommRing S]
  {m : ℕ}
  {r : Fin m → S}
  {k : Fin m → ℕ}
  {ε : ∀ a : Fin m, Fin (k a) → Localization.Away (r a)}
  -- given
  (hr : Ideal.span (Set.range r) = ⊤)
  (hε₁ : ∀ a i, IsIdempotentElem (ε a i))
  (hε₂ : ∀ a, ∑ i, ε a i = 1)
  (hε₃ : ∀ a i j, i ≠ j → ε a i * ε a j = 0) :
  -- imply
  ∃ (m' : ℕ) (t : Fin m' → S), Ideal.span (Set.range t) = ⊤ ∧ ∀ b : Fin m', ∃ (a : Fin m) (i : Fin (k a)) (ρ : Localization.Away (r a) →+* Localization.Away (t b)), ρ.comp (algebraMap S (Localization.Away (r a))) = algebraMap S (Localization.Away (t b)) ∧ ρ (ε a i) = 1 ∧ ∀ j : Fin (k a), j ≠ i → ρ (ε a j) = 0 := by
  -- proof
  classical
  let s : ∀ a : Fin m, Fin (k a) → S := fun a i => (IsLocalization.Away.sec (r a) (ε a i)).1
  let n : ∀ a : Fin m, Fin (k a) → ℕ := fun a i => (IsLocalization.Away.sec (r a) (ε a i)).2
  have hsec : ∀ a i, ε a i * algebraMap S (Localization.Away (r a)) (r a ^ n a i) = algebraMap S (Localization.Away (r a)) (s a i) := fun a i => IsLocalization.Away.sec_spec (r a) (ε a i)
  let ι := Σ a : Fin m, Fin (k a)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let t : Fin (Fintype.card ι) → S := fun b => r (e.symm b).1 * s (e.symm b).1 (e.symm b).2
  have ht : ∀ a i, t (e ⟨a, i⟩) = r a * s a i := fun a i => by
    show r (e.symm (e ⟨a, i⟩)).1 * s (e.symm (e ⟨a, i⟩)).1 (e.symm (e ⟨a, i⟩)).2 = r a * s a i
    rw [Equiv.symm_apply_apply]
  have hpow : ∀ a : Fin m, ∃ N : ℕ, r a ^ N ∈ Ideal.span (Set.range t) := by
    intro a
    set L := Localization.Away (r a)
    set M : ℕ := ∑ i, n a i with hM
    have hle : ∀ i, n a i ≤ M := fun i => by
      rw [hM]
      apply Finset.single_le_sum (f := fun i => n a i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h1 : ∀ i, ε a i * algebraMap S L (r a ^ M) = algebraMap S L (s a i * r a ^ (M - n a i)) := by
      intro i
      rw [map_mul, ← hsec a i, mul_assoc, ← map_mul, ← pow_add, Nat.add_sub_cancel' (hle i)]
    have h2 : algebraMap S L (r a ^ M) = algebraMap S L (∑ i, s a i * r a ^ (M - n a i)) := by
      rw [map_sum, ← Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.sum_mul, hε₂ a, one_mul]
    obtain ⟨⟨c, hc⟩, hc'⟩ := Iff.mp (IsLocalization.eq_iff_exists (Submonoid.powers (r a)) L) h2
    obtain ⟨K, rfl⟩ := Iff.mp (Submonoid.mem_powers_iff _ _) hc
    refine ⟨K + M + 1, ?_⟩
    have hpowEq : r a ^ (K + M + 1) = ∑ i, (r a * s a i) * (r a ^ K * r a ^ (M - n a i)) := by
      rw [pow_succ, pow_add, show r a ^ K * r a ^ M = r a ^ K * ∑ i, s a i * r a ^ (M - n a i) from hc', Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hpowEq]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨e ⟨a, i⟩, ht a i⟩)
  have hspan : Ideal.span (Set.range t) = ⊤ := by
    choose N hN using hpow
    set Nmax := Finset.univ.sup N
    have hNle : ∀ a, N a ≤ Nmax := fun a => Finset.le_sup (f := N) (Finset.mem_univ a)
    rw [eq_top_iff, ← Ideal.span_pow_eq_top (Set.range r) hr Nmax]
    refine Iff.mpr Ideal.span_le ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    show r a ^ Nmax ∈ Ideal.span (Set.range t)
    have hsplit : r a ^ Nmax = r a ^ (Nmax - N a) * r a ^ N a := by
      rw [← pow_add, Nat.sub_add_cancel (hNle a)]
    rw [hsplit]
    apply Ideal.mul_mem_left _ _ (hN a)
  refine ⟨Fintype.card ι, t, hspan, fun b => ?_⟩
  set a := (e.symm b).1
  set i := (e.symm b).2
  have htb : t b = r a * s a i := rfl
  set L := Localization.Away (r a)
  set T := Localization.Away (t b)
  have hunit_t : IsUnit (algebraMap S T (t b)) := IsLocalization.Away.algebraMap_isUnit (t b)
  have hunit_rs : IsUnit (algebraMap S T (r a) * algebraMap S T (s a i)) := by
    rw [← map_mul, ← htb]
    apply hunit_t
  have hunit_r : IsUnit (algebraMap S T (r a)) := isUnit_of_mul_isUnit_left hunit_rs
  have hunit_s : IsUnit (algebraMap S T (s a i)) := isUnit_of_mul_isUnit_right hunit_rs
  let ρ : L →+* T := IsLocalization.Away.lift (r a) (g := algebraMap S T) hunit_r
  have hρ : ∀ x : S, ρ (algebraMap S L x) = algebraMap S T x := fun x => IsLocalization.Away.lift_eq (r a) hunit_r x
  have hρcomp : ρ.comp (algebraMap S L) = algebraMap S T := RingHom.ext hρ
  have hρi : ρ (ε a i) = 1 := by
    apply eq_one_of_idem_unit ((hε₁ a i).map ρ)
    have h := congrArg ρ (hsec a i)
    rw [map_mul, hρ, hρ, map_pow] at h
    apply isUnit_of_mul_isUnit_left _
    rw [h]
    apply hunit_s
  refine ⟨a, i, ρ, hρcomp, hρi, fun j hj => ?_⟩
  rw [← mul_one (ρ (ε a j)), ← hρi, ← map_mul, hε₃ a j i hj, map_zero]


-- created on 2026-10-20
