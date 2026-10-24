import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[IsLocalRing_moduleFinite_quotient_maximalIdeal_pow_of_residueField_map_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_moduleFinite_quotient_maximalIdeal_pow_of_residueField_map_surjective.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [IsNoetherianRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R S))) (k : ℕ) :
  -- imply
  Module.Finite R (S ⧸ IsLocalRing.maximalIdeal S ^ k) := by
  -- proof
  classical
  set 𝔪 : Ideal S := IsLocalRing.maximalIdeal S with h𝔪
  have hlift : ∀ a : S, ∃ r : R, a - algebraMap R S r ∈ 𝔪 := fun a => by
    obtain ⟨ρ, hρ⟩ := hres (IsLocalRing.residue S a)
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective ρ
    rw [IsLocalRing.ResidueField.map_residue] at hρ
    exact ⟨r, Ideal.Quotient.eq.mp hρ.symm⟩
  induction k
  ·
    let _ : Subsingleton (S ⧸ 𝔪 ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    apply Module.Finite.of_surjective (Algebra.linearMap R (S ⧸ 𝔪 ^ 0)) fun q => ⟨0, Subsingleton.elim _ _⟩
  ·
    rename_i k ih
    have hle : 𝔪 ^ (k + 1) ≤ 𝔪 ^ k := Ideal.pow_le_pow_right (Nat.le_succ k)
    let π : (S ⧸ 𝔪 ^ (k + 1)) →ₐ[R] (S ⧸ 𝔪 ^ k) := Ideal.Quotient.factorₐ R hle
    have hπ : ∀ s : S, π (Ideal.Quotient.mk (𝔪 ^ (k + 1)) s) = Ideal.Quotient.mk (𝔪 ^ k) s := fun s => rfl
    rw [Module.finite_def]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker π.toLinearMap ?_ ?_
    ·
      have hsurjπ : Function.Surjective π.toLinearMap := fun q => by
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
        exact ⟨Ideal.Quotient.mk _ s, hπ s⟩
      rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsurjπ]
      apply Module.finite_def.mp ih
    ·
      rw [top_inf_eq]
      obtain ⟨G, hG⟩ := IsNoetherian.noetherian (𝔪 ^ k)
      have hker : LinearMap.ker π.toLinearMap =
          Submodule.span R ((Ideal.Quotient.mk (𝔪 ^ (k + 1))) '' (G : Set S)) := by
        apply le_antisymm
        ·
          intro q hq
          obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
          have hs : s ∈ 𝔪 ^ k := by
            rw [LinearMap.mem_ker] at hq
            change π (Ideal.Quotient.mk (𝔪 ^ (k + 1)) s) = 0 at hq
            rw [hπ] at hq
            apply Ideal.Quotient.eq_zero_iff_mem.mp hq
          clear hq
          rw [← hG] at hs
          induction hs using Submodule.span_induction
          ·
            rename_i x hx
            refine Submodule.subset_span ⟨x, hx, rfl⟩
          ·
            rw [map_zero]
            apply Submodule.zero_mem _
          ·
            rename_i x y _ _ hx hy
            rw [map_add]
            apply Submodule.add_mem _ hx hy
          ·
            rename_i a x hx ihx
            obtain ⟨r, hr⟩ := hlift a
            have hx' : x ∈ 𝔪 ^ k := hG ▸ hx
            have hm : (a - algebraMap R S r) * x ∈ 𝔪 ^ (k + 1) := by
              rw [pow_succ']
              apply Ideal.mul_mem_mul hr hx'
            have hsplit : Ideal.Quotient.mk (𝔪 ^ (k + 1)) (a • x) = r • Ideal.Quotient.mk (𝔪 ^ (k + 1)) x := by
              rw [smul_eq_mul, show a * x = algebraMap R S r * x + (a - algebraMap R S r) * x by ring, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hm, add_zero, map_mul, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap]
            rw [hsplit]
            apply Submodule.smul_mem _ r ihx
        ·
          rw [Submodule.span_le]
          rintro _ ⟨g, hg, rfl⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker]
          change π (Ideal.Quotient.mk (𝔪 ^ (k + 1)) g) = 0
          rw [hπ]
          apply Ideal.Quotient.eq_zero_iff_mem.mpr (hG ▸ Submodule.subset_span hg)
      rw [hker]
      apply Submodule.fg_span ((G.finite_toSet).image _)


-- created on 2026-10-20
