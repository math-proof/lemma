import Mathlib
import sympy.Basic

open Module

/--
[AddCommGroup_moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddCommGroup_moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul.lean)
-/

def Saturated
  {R : Type*}
  [AddCommGroup R]
  (S : AddSubgroup R) : Prop := ∀ (k : ℤ) (x : R), k ≠ 0 → k • x ∈ S → x ∈ S

private lemma  saturated_of_iff
    {R : Type*}
    [AddCommGroup R]
    {M M' : AddSubgroup R}
    (h : ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M) : M ≤ M' ∧ Saturated M' := by
  refine ⟨fun x hx => (h x).2 ⟨1, one_ne_zero, by simpa using hx⟩, ?_⟩
  intro k x hk hkx
  obtain ⟨k', hk', hk'x⟩ := (h _).1 hkx
  exact (h x).2 ⟨k' * k, mul_ne_zero hk' hk, by simpa [mul_smul] using hk'x⟩


(hρ : ∀ x : R, ρ x = 0 → ∃ y : R, x = n • y)

include hρ in

private lemma  pow_finrank_le_card
  {R : Type*}
  [AddCommGroup R]
  [IsAddTorsionFree R]
  {G : Type*}
  [AddCommGroup G]
  [Finite G]
  (ρ : R →+ G)
  (n : ℕ)
  (S : AddSubgroup R) (hS : Saturated S) (hfg : S.FG) (hn : n ≠ 0) :
  n ^ finrank ℤ S ≤ Nat.card G := by
haveI : Module.Finite ℤ S :=
  Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg S).mpr hfg)
haveI : IsAddTorsionFree S := inferInstance
haveI : Module.Free ℤ S := Module.free_of_finite_type_torsion_free'

set ρ' : S →+ G := ρ.comp S.subtype with hρ'

have hker : ρ'.ker ≤ (nsmulAddMonoidHom (α := S) n).range := by
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  obtain ⟨y, hy⟩ := hρ (x : R) hx
  have hyS : y ∈ S := by
    refine hS n y (by exact_mod_cast hn) ?_
    rw [natCast_zsmul, ← hy]
    exact x.2
  refine ⟨⟨y, hyS⟩, ?_⟩
  apply Subtype.ext
  simp [hy]
have h1 : (nsmulAddMonoidHom (α := S) n).range.index = n ^ finrank ℤ S :=
  AddSubgroup.index_range_nsmul S n
have h2 : (nsmulAddMonoidHom (α := S) n).range.index ∣ ρ'.ker.index :=
  AddSubgroup.index_dvd_of_le hker
have h3 : ρ'.ker.index = Nat.card ρ'.range := AddSubgroup.index_ker ρ'
have h4 : Nat.card ρ'.range ≤ Nat.card G :=
  Nat.card_le_card_of_injective _ Subtype.val_injective
have h5 : Nat.card ρ'.range ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨0, zero_mem _⟩, inferInstance⟩
calc n ^ finrank ℤ S = (nsmulAddMonoidHom (α := S) n).range.index := h1.symm
  _ ≤ ρ'.ker.index := Nat.le_of_dvd (by rw [h3]; exact Nat.pos_of_ne_zero h5) h2
  _ = Nat.card ρ'.range := h3
  _ ≤ Nat.card G := h4

private lemma  linearIndependent_cod
    {R : Type*}
    [AddCommGroup R]
    {ι : Type*} (S : AddSubgroup R) (v : ι → R)
    (hv : LinearIndependent ℤ v) (hmem : ∀ i, v i ∈ S) :
    LinearIndependent ℤ (fun i => (⟨v i, hmem i⟩ : S)) := by
  refine LinearIndependent.of_comp S.subtype.toIntLinearMap ?_
  exact hv

private lemma  main
    {R : Type*}
    [AddCommGroup R]
    [IsAddTorsionFree R]
    (hsat : ∀ M : AddSubgroup R, M.FG →
      ∃ M' : AddSubgroup R, M'.FG ∧ ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M)
    {G : Type*} [AddCommGroup G] [Finite G] (ρ : R →+ G) (n : ℕ) (hn : 1 < n)
    (hρ : ∀ x : R, ρ x = 0 → ∃ y : R, x = n • y) :
    Module.Finite ℤ R ∧ Module.Free ℤ R := by
  classical
  have hn0 : n ≠ 0 := by omega

  have hbound : ∀ s : Finset R, LinearIndependent ℤ ((↑) : s → R) → s.card < Nat.card G := by
    intro s hs
    obtain ⟨M', hM'fg, hM'⟩ := hsat (Submodule.span ℤ (s : Set R)).toAddSubgroup
      (by
        rw [← Submodule.fg_iff_addSubgroup_fg]
        exact Submodule.fg_span s.finite_toSet)
    obtain ⟨hle, hsatM'⟩ := saturated_of_iff hM'
    have hmem : ∀ i : s, (i : R) ∈ M' := fun i =>
      hle (Submodule.subset_span (by exact_mod_cast i.2))
    haveI : Module.Finite ℤ M' :=
      Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg M').mpr hM'fg)
    have hli : LinearIndependent ℤ (fun i : s => (⟨(i : R), hmem i⟩ : M')) :=
      linearIndependent_cod M' _ hs hmem
    have hcard : s.card ≤ finrank ℤ M' := by
      simpa using hli.fintype_card_le_finrank
    have hpow : n ^ finrank ℤ M' ≤ Nat.card G := pow_finrank_le_card ρ n hρ M' hsatM' hM'fg hn0
    calc s.card < n ^ s.card := Nat.lt_pow_self hn
      _ ≤ n ^ finrank ℤ M' := Nat.pow_le_pow_right (by omega) hcard
      _ ≤ Nat.card G := hpow

  obtain ⟨I, hIli, hImax⟩ := exists_maximal_linearIndepOn ℤ (id : R → R)
  have hIfin : I.Finite := by
    by_contra hinf
    obtain ⟨t, htI, htcard⟩ := Set.Infinite.exists_subset_card_eq hinf (Nat.card G)
    have hli : LinearIndependent ℤ ((↑) : t → R) := by
      have := hIli.mono htI
      exact this.linearIndependent
    exact absurd (htcard ▸ hbound t hli) (lt_irrefl _)

  set M : AddSubgroup R := (Submodule.span ℤ I).toAddSubgroup with hMdef
  have hMfg : M.FG := by
    rw [hMdef, ← Submodule.fg_iff_addSubgroup_fg]
    exact Submodule.fg_span hIfin
  obtain ⟨M', hM'fg, hM'⟩ := hsat M hMfg
  obtain ⟨hle, hsatM'⟩ := saturated_of_iff hM'
  have htop : M' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_cases hx : x ∈ I
    · exact hle (Submodule.subset_span hx)
    · obtain ⟨a, ha, hax⟩ := hImax x hx
      refine hsatM' a x ha (hle ?_)
      simpa [hMdef] using hax
  have hfgtop : (⊤ : AddSubgroup R).FG := htop ▸ hM'fg
  haveI hfin : Module.Finite ℤ R :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_def).mpr hfgtop)
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩
@[main]
private lemma main
  [AddCommGroup R] [IsAddTorsionFree R] [AddCommGroup G] [Finite G]
  {ρ : R →+ G}
  {n : ℕ}
-- given
  (hsat : ∀ M : AddSubgroup R, M.FG → ∃ M' : AddSubgroup R, M'.FG ∧ ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M)
  (hn : 1 < n)
  (hρ : ∀ x : R, ρ x = 0 → ∃ y : R, x = n • y) :
-- imply
  Module.Finite ℤ R ∧ Module.Free ℤ R :=
-- proof
  main hsat ρ n hn hρ


-- created on 2026-10-09
