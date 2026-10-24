import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma eq_zero_of_forall_pow_mul_eq_zero
  {A' : Type u} [CommRing A']
  {N : ℕ} {s : Fin N → A'} {x : A'}
  -- given
  (hs : Ideal.span (Set.range s) = ⊤)
  (h : ∀ k, ∃ n : ℕ, s k ^ n * x = 0) :
  -- imply
  x = 0 := by
  -- proof
  classical
  choose n hn using h
  let m : ℕ := Finset.univ.sup n
  have hm : ∀ k, s k ^ m * x = 0 := by
    intro k
    have hk : n k ≤ m := Finset.le_sup (Finset.mem_univ k)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    rw [hd, pow_add, mul_comm (s k ^ n k), mul_assoc, hn k, mul_zero]
  have htop : Ideal.span (Set.range fun k => s k ^ m) = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range s) hs m
    rwa [← Set.range_comp] at this
  obtain ⟨c, hc⟩ := Iff.mp Ideal.mem_span_range_iff_exists_fun (htop.symm ▸ Submodule.mem_top : (1 : A') ∈ Ideal.span (Set.range fun k => s k ^ m))
  calc
    _ = (∑ k, c k * s k ^ m) * x := by rw [hc, one_mul]
    _ = ∑ k, c k * (s k ^ m * x) := by
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    _ = 0 := by simp only [hm, mul_zero, Finset.sum_const_zero]

private lemma IdealCutAux.finite_case
  {A : Type u} [CommRing A]
  {P : ∀ (A' : Type u) [CommRing A'], (A →+* A') → Prop}
  {N : ℕ} {r : Fin N → A}
  {K : ∀ i : Fin N, Ideal (Localization.Away (r i))}
  -- given
  (hPmap : ∀ (A' A'' : Type u) [CommRing A'] [CommRing A''] (χ : A' →+* A'') (φ : A →+* A'), P A' φ → P A'' (χ.comp φ))
  (hPloc : ∀ (A' : Type u) [CommRing A'] (φ : A →+* A') (κ : Type u) (s : κ → A'), Ideal.span (Set.range s) = ⊤ → (∀ k, P (Localization.Away (s k)) ((algebraMap A' (Localization.Away (s k))).comp φ)) → P A' φ)
  (hr : Ideal.span (Set.range r) = ⊤)
  (hK : ∀ (i : Fin N) (A' : Type u) [CommRing A'] (χ : Localization.Away (r i) →+* A'), P A' (χ.comp (algebraMap A (Localization.Away (r i)))) ↔ Ideal.map χ (K i) = ⊥) :
  -- imply
  ∃ I : Ideal A, ∀ (A' : Type u) [CommRing A'] (φ : A →+* A'), P A' φ ↔ Ideal.map φ I = ⊥ := by
  -- proof
  classical
  let lam : ∀ i : Fin N, A →+* Localization.Away (r i) := fun i => algebraMap A (Localization.Away (r i))
  let I : Ideal A := ⨅ i, (K i).comap (lam i)
  have hI : ∀ a : A, a ∈ I ↔ ∀ i, lam i a ∈ K i := by
    intro a
    simp only [I, Ideal.mem_iInf, Ideal.mem_comap]
  have compat : ∀ (i j : Fin N) (a : A), lam i a ∈ K i → ∃ m : ℕ, lam j (r i ^ m * a) ∈ K j := by
    intro i j a ha
    let Q := Localization.Away (r j) ⧸ K j
    let π : Localization.Away (r j) →+* Q := Ideal.Quotient.mk (K j)
    have hP1 : P Q (π.comp (lam j)) := by
      apply Iff.mpr (hK j Q π)
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    let Qi := Localization.Away (π (lam j (r i)))
    let ψ : A →+* Qi := (algebraMap Q Qi).comp (π.comp (lam j))
    have hP2 : P Qi ψ := hPmap Q Qi (algebraMap Q Qi) _ hP1
    have hunit : IsUnit (ψ (r i)) := IsLocalization.Away.algebraMap_isUnit (π (lam j (r i)))
    let χ : Localization.Away (r i) →+* Qi := IsLocalization.Away.lift (r i) hunit
    have hχ : χ.comp (lam i) = ψ := IsLocalization.Away.lift_comp (r i) hunit
    have hP3 : P Qi (χ.comp (lam i)) := by
      rw [hχ]
      apply hP2
    have hKi : Ideal.map χ (K i) = ⊥ := Iff.mp (hK i Qi χ) hP3
    have h0 : ψ a = 0 := by
      rw [← hχ, RingHom.comp_apply]
      have : χ (lam i a) ∈ Ideal.map χ (K i) := Ideal.mem_map_of_mem _ ha
      rwa [hKi, Ideal.mem_bot] at this
    obtain ⟨⟨c, hc⟩, hca⟩ := Iff.mp (IsLocalization.map_eq_zero_iff (Submonoid.powers (π (lam j (r i)))) Qi _) h0
    obtain ⟨m, rfl⟩ := Iff.mp (Submonoid.mem_powers_iff _ _) hc
    refine ⟨m, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_mul, map_pow]
    apply hca
  have sat : ∀ (i : Fin N) (a : A), lam i a ∈ K i → ∃ m : ℕ, r i ^ m * a ∈ I := by
    intro i a ha
    choose m hm using fun j => compat i j a ha
    refine ⟨Finset.univ.sup m, Iff.mpr (hI _) fun j => ?_⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := m) (Finset.mem_univ j))
    rw [hd, add_comm, pow_add, mul_assoc, map_mul]
    apply Ideal.mul_mem_left _ _ (hm j)
  have desc : ∀ i, Ideal.map (lam i) I = K i := by
    intro i
    apply le_antisymm
    ·
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      apply Iff.mp (hI a) ha i
    ·
      intro k hk
      obtain ⟨⟨a, s⟩, hks⟩ := IsLocalization.surj (Submonoid.powers (r i)) k
      obtain ⟨n, hn⟩ := Iff.mp (Submonoid.mem_powers_iff _ _) s.2
      have ha : lam i a ∈ K i := by
        rw [← hks]
        apply Ideal.mul_mem_right _ _ hk
      obtain ⟨m, hm⟩ := sat i a ha
      have hu : IsUnit (lam i (r i ^ (m + n))) := by
        rw [map_pow]
        apply (IsLocalization.Away.algebraMap_isUnit (r i)).pow _
      obtain ⟨u, hu'⟩ := hu
      have hks' : k * lam i (r i ^ n) = lam i a := by
        rw [hn]
        apply hks
      have e1 : lam i (r i ^ m * a) = k * ↑u := by
        rw [hu', map_mul, ← hks', pow_add, map_mul]
        ring
      have hk' : k = lam i (r i ^ m * a) * ↑u⁻¹ := by
        rw [e1, mul_assoc, Units.mul_inv, mul_one]
      rw [hk']
      apply Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hm)
  refine ⟨I, fun A' _ φ => ?_⟩
  have fact : ∀ i, ∃ χ : Localization.Away (r i) →+* Localization.Away (φ (r i)), χ.comp (lam i) = (algebraMap A' (Localization.Away (φ (r i)))).comp φ := fun i =>
    ⟨IsLocalization.Away.lift (r i) (g := (algebraMap A' (Localization.Away (φ (r i)))).comp φ)
      (IsLocalization.Away.algebraMap_isUnit (φ (r i))), IsLocalization.Away.lift_comp _ _⟩
  have hspan : Ideal.span (Set.range fun k => φ (r k)) = ⊤ := by
    have := congrArg (Ideal.map φ) hr
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  constructor
  ·
    intro hP
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    rw [RingHom.mem_ker]
    apply eq_zero_of_forall_pow_mul_eq_zero (s := fun k => φ (r k)) hspan
    intro k
    obtain ⟨χ, hχ⟩ := fact k
    have hPk : P _ (χ.comp (lam k)) := by
      rw [hχ]
      apply hPmap _ _ _ _ hP
    have hKk := Iff.mp (hK k _ χ) hPk
    have h0 : (algebraMap A' (Localization.Away (φ (r k)))) (φ a) = 0 := by
      have : χ (lam k a) ∈ Ideal.map χ (K k) := Ideal.mem_map_of_mem _ (Iff.mp (hI a) ha k)
      rw [hKk, Ideal.mem_bot] at this
      rw [← RingHom.comp_apply, ← hχ, RingHom.comp_apply]
      apply this
    obtain ⟨⟨c, hc⟩, hca⟩ := Iff.mp (IsLocalization.map_eq_zero_iff (Submonoid.powers (φ (r k))) _ _) h0
    obtain ⟨n, rfl⟩ := Iff.mp (Submonoid.mem_powers_iff _ _) hc
    refine ⟨n, hca⟩
  ·
    intro hIφ
    refine hPloc A' φ (ULift (Fin N) : Type u) (fun k => φ (r k.down)) ?_ ?_
    ·
      have : (fun k : (ULift (Fin N) : Type u) => φ (r k.down)) = (fun k => φ (r k)) ∘ ULift.down := rfl
      rw [this, ULift.down_surjective.range_comp]
      apply hspan
    ·
      intro k'
      obtain ⟨k⟩ := k'
      obtain ⟨χ, hχ⟩ := fact k
      show P _ ((algebraMap A' (Localization.Away (φ (r k)))).comp φ)
      rw [← hχ]
      apply Iff.mpr (hK k _ χ)
      rw [← desc k, Ideal.map_map, hχ, ← Ideal.map_map, hIφ, Ideal.map_bot]

/--
[Ideal_exists_forall_iff_map_eq_bot_of_forall_away](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_forall_iff_map_eq_bot_of_forall_away.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A]
  {P : ∀ (A' : Type u) [CommRing A'], (A →+* A') → Prop}
  {κ : Type u} {r : κ → A}
  {K : ∀ i : κ, Ideal (Localization.Away (r i))}
  -- given
  (hPmap : ∀ (A' A'' : Type u) [CommRing A'] [CommRing A''] (χ : A' →+* A'') (φ : A →+* A'), P A' φ → P A'' (χ.comp φ))
  (hPloc : ∀ (A' : Type u) [CommRing A'] (φ : A →+* A') (κ : Type u) (s : κ → A'), Ideal.span (Set.range s) = ⊤ → (∀ k, P (Localization.Away (s k)) ((algebraMap A' (Localization.Away (s k))).comp φ)) → P A' φ)
  (hr : Ideal.span (Set.range r) = ⊤)
  (hK : ∀ (i : κ) (A' : Type u) [CommRing A'] (χ : Localization.Away (r i) →+* A'), P A' (χ.comp (algebraMap A (Localization.Away (r i)))) ↔ Ideal.map χ (K i) = ⊥) :
  -- imply
  ∃ I : Ideal A, ∀ (A' : Type u) [CommRing A'] (φ : A →+* A'), P A' φ ↔ Ideal.map φ I = ⊥ := by
  -- proof
  classical
  have h1 : (1 : A) ∈ Ideal.span (Set.range r) := by
    rw [hr]
    trivial
  obtain ⟨T, hTsub, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hpre : ∀ t : T, ∃ i : κ, r i = t := fun t => hTsub t.2
  choose idx hidx using hpre
  let N := T.card
  let e : Fin N → κ := fun k => idx (T.equivFin.symm k)
  apply IdealCutAux.finite_case (A := A) (P := P) hPmap hPloc (N := N) (r := fun k => r (e k)) _ (K := fun k => K (e k)) (fun k => hK (e k))
  rw [Ideal.eq_top_iff_one]
  have hrange : Set.range (fun k => r (e k)) = (T : Set A) := by
    ext a
    constructor
    ·
      intro hk
      obtain ⟨k, rfl⟩ := hk
      show r (idx (T.equivFin.symm k)) ∈ (T : Set A)
      rw [hidx]
      apply (T.equivFin.symm k).2
    ·
      intro ha
      refine ⟨T.equivFin ⟨a, ha⟩, by simp [e, hidx]⟩
  rw [hrange]
  apply h1T


-- created on 2026-10-20
