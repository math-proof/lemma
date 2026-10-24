import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma exists_not_mem_mul_le_of_map_le
  {S B Bp : Type} [CommRing S] [CommRing B] [CommRing Bp] [Algebra B Bp]
  {𝔭 : Ideal S} [𝔭.IsPrime]
  {φ : S →+* B} [IsLocalization (𝔭.primeCompl.map φ.toMonoidHom) Bp]
  {J₁ J₂ : Ideal B}
  -- given
  (h₀ : J₁.FG)
  (h : J₁.map (algebraMap B Bp) ≤ J₂.map (algebraMap B Bp)) :
  -- imply
  ∃ s : S, s ∉ 𝔭 ∧ ∀ x ∈ J₁, φ s * x ∈ J₂ := by
  -- proof
  classical
  obtain ⟨gens, hgens⟩ := h₀
  have key : ∀ x ∈ J₁, ∃ s : S, s ∉ 𝔭 ∧ φ s * x ∈ J₂ := by
    intro x hx
    have hx' : algebraMap B Bp x ∈ J₂.map (algebraMap B Bp) := h (Ideal.mem_map_of_mem _ hx)
    obtain ⟨⟨a, t⟩, hat⟩ := Iff.mp (IsLocalization.mem_map_algebraMap_iff (𝔭.primeCompl.map φ.toMonoidHom) Bp) hx'
    have hat' : algebraMap B Bp (x * (t : B)) = algebraMap B Bp (a : B) := by
      rw [map_mul]
      apply hat
    obtain ⟨c, hc⟩ := Iff.mp (IsLocalization.eq_iff_exists (𝔭.primeCompl.map φ.toMonoidHom) Bp) hat'
    obtain ⟨sc, hsc, hscq⟩ := Iff.mp Submonoid.mem_map c.2
    obtain ⟨st, hst, hstq⟩ := Iff.mp Submonoid.mem_map t.2
    refine ⟨sc * st, ?_, ?_⟩
    ·
      intro hmem
      obtain h' | h' := Ideal.IsPrime.mem_or_mem ‹𝔭.IsPrime› hmem
      · apply hsc h'
      · apply hst h'
    ·
      have : φ (sc * st) * x = (c : B) * (x * (t : B)) := by
        rw [map_mul, show φ sc = (c : B) from hscq, show φ st = ((t : _) : B) from hstq]
        ring
      rw [this, hc]
      apply J₂.mul_mem_left _ a.2
  choose sf hsf using key
  refine ⟨∏ x ∈ gens.attach, sf x.1 (hgens ▸ Ideal.subset_span x.2), ?_, ?_⟩
  ·
    refine Finset.prod_induction _ (fun y : S => y ∉ 𝔭) ?_ ?_ ?_
    ·
      intro a b ha hb hab
      obtain h' | h' := Ideal.IsPrime.mem_or_mem ‹𝔭.IsPrime› hab
      · apply ha h'
      · apply hb h'
    · apply Iff.mp (Ideal.ne_top_iff_one 𝔭) (Ideal.IsPrime.ne_top ‹_›)
    ·
      intro x _
      apply (hsf x.1 _).1
  ·
    intro x hx
    rw [← hgens] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    ·
      intro y hy
      obtain ⟨rest, hrest⟩ : ∃ rest : S, (∏ x ∈ gens.attach, sf x.1 (hgens ▸ Ideal.subset_span x.2)) = sf y (hgens ▸ Ideal.subset_span hy) * rest := by
        refine ⟨∏ x ∈ (gens.attach.erase ⟨y, hy⟩), sf x.1 (hgens ▸ Ideal.subset_span x.2), ?_⟩
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_attach _ ⟨y, hy⟩)]
      rw [hrest, map_mul, mul_comm (φ _) (φ rest), mul_assoc]
      apply J₂.mul_mem_left _ (hsf y _).2
    · simp
    ·
      intro y z _ _ hy hz
      rw [mul_add]
      apply J₂.add_mem hy hz
    ·
      intro r y _ hy
      rw [smul_eq_mul, mul_left_comm]
      apply J₂.mul_mem_left _ hy

private lemma exists_not_mem_map_eq_map
  {S B Bp : Type} [CommRing S] [CommRing B] [CommRing Bp] [Algebra B Bp]
  {𝔭 : Ideal S} [𝔭.IsPrime]
  {φ : S →+* B} [IsLocalization (𝔭.primeCompl.map φ.toMonoidHom) Bp]
  {J₁ J₂ : Ideal B}
  -- given
  (h₀ : J₁.FG)
  (h₁ : J₂.FG)
  (h : J₁.map (algebraMap B Bp) = J₂.map (algebraMap B Bp)) :
  -- imply
  ∃ g : S, g ∉ 𝔭 ∧ ∀ (Bg : Type) [CommRing Bg] [Algebra B Bg] [IsLocalization (Submonoid.powers (φ g)) Bg], J₁.map (algebraMap B Bg) = J₂.map (algebraMap B Bg) := by
  -- proof
  obtain ⟨s₁, hs₁, H₁⟩ := exists_not_mem_mul_le_of_map_le (φ := φ) (𝔭 := 𝔭) h₀ h.le
  obtain ⟨s₂, hs₂, H₂⟩ := exists_not_mem_mul_le_of_map_le (φ := φ) (𝔭 := 𝔭) (J₁ := J₂) (J₂ := J₁) h₁ h.ge
  refine ⟨s₁ * s₂, ?_, ?_⟩
  ·
    intro hmem
    obtain h' | h' := Ideal.IsPrime.mem_or_mem ‹𝔭.IsPrime› hmem
    · apply hs₁ h'
    · apply hs₂ h'
  intro Bg _ _ _
  have hunit : IsUnit (algebraMap B Bg (φ (s₁ * s₂))) :=
    IsLocalization.map_units Bg (⟨φ (s₁ * s₂), Submonoid.mem_powers _⟩ : Submonoid.powers (φ (s₁ * s₂)))
  have hu₁ : IsUnit (algebraMap B Bg (φ s₁)) := by
    rw [map_mul, map_mul] at hunit
    apply isUnit_of_mul_isUnit_left hunit
  have hu₂ : IsUnit (algebraMap B Bg (φ s₂)) := by
    rw [map_mul, map_mul] at hunit
    apply isUnit_of_mul_isUnit_right hunit
  apply le_antisymm
  ·
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    rw [show algebraMap B Bg x = hu₁.unit⁻¹ * algebraMap B Bg (φ s₁ * x) by rw [map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]]
    apply Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (H₁ x hx))
  ·
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    rw [show algebraMap B Bg x = hu₂.unit⁻¹ * algebraMap B Bg (φ s₂ * x) by rw [map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]]
    apply Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (H₂ x hx))

/--
[Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg.lean)
-/
@[path]
private lemma main
  {S B : Type} [CommRing S] [CommRing B]
  {𝔭 : Ideal S} [𝔭.IsPrime]
  {φ : S →+* B} {Bₚ : Type} [CommRing Bₚ] [Algebra B Bₚ] [IsLocalization (𝔭.primeCompl.map φ.toMonoidHom) Bₚ]
  {J₁ J₂ : Ideal B}
  -- given
  (h₀ : J₁.FG)
  (h₁ : J₂.FG)
  (h : J₁.map (algebraMap B Bₚ) = J₂.map (algebraMap B Bₚ)) :
  -- imply
  ∃ g : S, g ∉ 𝔭 ∧ ∀ (B' : Type) [CommRing B'] [Algebra B B'] [IsLocalization.Away (φ g) B'], J₁.map (algebraMap B B') = J₂.map (algebraMap B B') := by
  -- proof
  apply exists_not_mem_map_eq_map (φ := φ) (𝔭 := 𝔭) (Bp := Bₚ) h₀ h₁ h


-- created on 2026-10-20
