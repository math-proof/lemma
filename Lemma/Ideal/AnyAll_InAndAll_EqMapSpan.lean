import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Ideal_exists_forall_map_localization_eq_span_of_finite_maximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_forall_map_localization_eq_span_of_finite_maximal.lean)
-/
@[path]
private lemma main
  {P : Type u} [CommRing P] [IsNoetherianRing P]
  {J : Ideal P}
  {N : ℕ}
  -- given
  (hfin : {𝔫 : Ideal P | 𝔫.IsMaximal ∧ J ≤ 𝔫}.Finite)
  (hloc : ∀ (𝔫 : Ideal P) [𝔫.IsMaximal], J ≤ 𝔫 → ∃ g : Fin N → P, (∀ i, g i ∈ J) ∧ Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) J = Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime 𝔫) (g i))) :
  -- imply
  ∃ f : Fin N → P, (∀ i, f i ∈ J) ∧ ∀ (𝔫 : Ideal P) [𝔫.IsMaximal], J ≤ 𝔫 → Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) J = Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime 𝔫) (f i)) := by
  -- proof
  classical
  set T : Set (Ideal P) := {𝔫 : Ideal P | 𝔫.IsMaximal ∧ J ≤ 𝔫} with hT
  have key : ∀ 𝔫 : Ideal P, 𝔫 ∈ T → ∃ g : Fin N → P, (∀ i, g i ∈ J) ∧ ∀ x ∈ J, ∃ s : P, s ∉ 𝔫 ∧ s * x ∈ Ideal.span (Set.range g) := by
    intro 𝔫 hT𝔫
    obtain ⟨hmax, hJ⟩ := hT𝔫
    let _ := hmax
    obtain ⟨g, hgJ, hg⟩ := hloc 𝔫 hJ
    refine ⟨g, hgJ, fun x hx => ?_⟩
    have h1 : algebraMap P (Localization.AtPrime 𝔫) x ∈ (Ideal.span (Set.range g)).map (algebraMap P (Localization.AtPrime 𝔫)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      change _ ∈ Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime 𝔫) (g i))
      rw [← hg]
      apply Ideal.mem_map_of_mem _ hx
    obtain ⟨⟨y, s⟩, hys⟩ := Iff.mp (IsLocalization.mem_map_algebraMap_iff 𝔫.primeCompl _) h1
    rw [← map_mul] at hys
    obtain ⟨c, hc⟩ := Iff.mp (IsLocalization.eq_iff_exists 𝔫.primeCompl _) hys
    refine ⟨c * s, 𝔫.primeCompl.mul_mem c.2 s.2, ?_⟩
    rw [show (c : P) * s * x = c * (x * s) by ring]
    change (c : P) * (x * ((y, s) : _ × _).2) ∈ _
    rw [hc]
    apply Ideal.mul_mem_left _ _ y.2
  choose! G hGJ hG using key
  have he : ∀ 𝔫 : Ideal P, 𝔫 ∈ T → ∃ e : P, e ∉ 𝔫 ∧ ∀ 𝔫' ∈ T, 𝔫' ≠ 𝔫 → e ∈ 𝔫' := by
    intro 𝔫 h𝔫
    have hpick : ∀ 𝔫' : Ideal P, 𝔫' ∈ hfin.toFinset.erase 𝔫 → ∃ a : P, a ∈ 𝔫' ∧ a ∉ 𝔫 := by
      intro 𝔫' h𝔫'
      obtain ⟨hne, h𝔫'F⟩ := Iff.mp Finset.mem_erase h𝔫'
      have h𝔫'T : 𝔫' ∈ T := Iff.mp (Set.Finite.mem_toFinset hfin) h𝔫'F
      by_contra hcon
      apply hne (h𝔫'T.1.eq_of_le h𝔫.1.ne_top fun x hx => by_contra fun hx' => hcon ⟨x, hx, hx'⟩)
    choose! a ha using hpick
    refine ⟨∏ 𝔫' ∈ hfin.toFinset.erase 𝔫, a 𝔫', ?_, ?_⟩
    ·
      refine Finset.prod_induction _ (fun x => x ∉ 𝔫) ?_ ?_ ?_
      ·
        intro x y hx hy hxy
        apply (h𝔫.1.isPrime.mem_or_mem hxy).elim hx hy
      ·
        intro h1
        apply h𝔫.1.ne_top (Iff.mpr (Ideal.eq_top_iff_one _) h1)
      ·
        intro 𝔫' h𝔫'
        apply (ha 𝔫' h𝔫').2
    ·
      intro 𝔫' h𝔫'T hne
      have hmem : 𝔫' ∈ hfin.toFinset.erase 𝔫 := Iff.mpr Finset.mem_erase ⟨hne, Iff.mpr (Set.Finite.mem_toFinset hfin) h𝔫'T⟩
      rw [← Finset.mul_prod_erase _ _ hmem]
      apply Ideal.mul_mem_right _ _ (ha 𝔫' hmem).1
  choose! E hE𝔫 hE using he
  let f : Fin N → P := fun i => ∑ 𝔫 ∈ hfin.toFinset, E 𝔫 * G 𝔫 i
  have hfJ : ∀ i, f i ∈ J := fun i => Ideal.sum_mem _ fun 𝔫 h𝔫 => J.mul_mem_left _ (hGJ 𝔫 (Iff.mp (Set.Finite.mem_toFinset hfin) h𝔫) i)
  refine ⟨f, hfJ, ?_⟩
  intro 𝔫 inst hJ𝔫
  have h𝔫T : 𝔫 ∈ T := ⟨inst, hJ𝔫⟩
  have h𝔫F : 𝔫 ∈ hfin.toFinset := Iff.mpr (Set.Finite.mem_toFinset hfin) h𝔫T
  set S := Localization.AtPrime 𝔫 with hS
  set M : Ideal S := J.map (algebraMap P S) with hM
  set N' : Ideal S := Ideal.span (Set.range fun i => algebraMap P S (f i)) with hN'
  have hN'eq : N' = (Ideal.span (Set.range f)).map (algebraMap P S) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hN'M : N' ≤ M := by
    rw [hN'eq]
    apply Ideal.map_mono (Iff.mpr Ideal.span_le (Iff.mpr Set.range_subset_iff hfJ))
  refine le_antisymm ?_ hN'M
  have h𝔫S : 𝔫.map (algebraMap P S) = IsLocalRing.maximalIdeal S := Localization.AtPrime.map_eq_maximalIdeal
  set K : Ideal S := N' ⊔ IsLocalRing.maximalIdeal S • M with hK
  have hK : ∀ i, algebraMap P S (G 𝔫 i) ∈ K := by
    intro i
    have hsplit : E 𝔫 * G 𝔫 i = f i - ∑ 𝔫' ∈ hfin.toFinset.erase 𝔫, E 𝔫' * G 𝔫' i := by
      rw [eq_sub_iff_add_eq]
      apply Finset.add_sum_erase _ (fun 𝔫' => E 𝔫' * G 𝔫' i) h𝔫F
    have hrest : ∑ 𝔫' ∈ hfin.toFinset.erase 𝔫, E 𝔫' * G 𝔫' i ∈ 𝔫 * J := by
      refine Ideal.sum_mem _ fun 𝔫' h𝔫' => ?_
      obtain ⟨hne, h𝔫'F⟩ := Iff.mp Finset.mem_erase h𝔫'
      have h𝔫'T : 𝔫' ∈ T := Iff.mp (Set.Finite.mem_toFinset hfin) h𝔫'F
      apply Ideal.mul_mem_mul (hE 𝔫' h𝔫'T 𝔫 h𝔫T hne.symm) (hGJ 𝔫' h𝔫'T i)
    have hunit : IsUnit (algebraMap P S (E 𝔫)) := IsLocalization.map_units S (⟨E 𝔫, hE𝔫 𝔫 h𝔫T⟩ : 𝔫.primeCompl)
    rw [← Ideal.unit_mul_mem_iff_mem _ hunit, ← map_mul, hsplit, map_sub]
    refine K.sub_mem (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
    · apply Ideal.subset_span (⟨i, rfl⟩ : algebraMap P S (f i) ∈ Set.range fun j => algebraMap P S (f j))
    ·
      rw [Ideal.smul_eq_mul, ← h𝔫S, hM, ← Ideal.map_mul]
      apply Ideal.mem_map_of_mem _ hrest
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian M) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  rw [hM, Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap]
  obtain ⟨s, hs𝔫, hsx⟩ := hG 𝔫 h𝔫T x hx
  have hunit : IsUnit (algebraMap P S s) := IsLocalization.map_units S (⟨s, hs𝔫⟩ : 𝔫.primeCompl)
  rw [← Ideal.unit_mul_mem_iff_mem _ hunit, ← map_mul]
  suffices hle : (Ideal.span (Set.range (G 𝔫))).map (algebraMap P S) ≤ K by
    apply hle (Ideal.mem_map_of_mem _ hsx)
  rw [Ideal.map_span, Ideal.span_le]
  intro z hz
  obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hz
  apply hK i


-- created on 2026-10-20
