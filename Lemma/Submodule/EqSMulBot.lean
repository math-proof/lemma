import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

/--
[Module_exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime.lean)
-/
@[path]
private lemma main
  (S : Type u) [CommRing S] (H : Type v) [AddCommGroup H] [Module S H] (hH : IsFiniteLength S H)
  (𝔭 : Ideal S) [𝔭.IsPrime]
  (B : Type w) [CommRing B] [Algebra S B] [IsLocalization.AtPrime B 𝔭] [IsLocalRing B] :
  -- imply
  ∃ n : ℕ, IsLocalRing.maximalIdeal B ^ n • (⊤ : Submodule B (B ⊗[S] H)) = ⊥ := by
  -- proof
  classical
  obtain ⟨hNoeth, hArt⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hH
  obtain ⟨N0, hN0mem, hN0min⟩ := IsArtinian.set_has_minimal (R := S) (M := H)
    (Set.range fun n : ℕ => (𝔭 ^ n • ⊤ : Submodule S H)) ⟨_, 0, rfl⟩
  obtain ⟨n, rfl⟩ := hN0mem
  have hle : (𝔭 ^ (n + 1) • ⊤ : Submodule S H) ≤ 𝔭 ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))
  have hstab : (𝔭 ^ (n + 1) • ⊤ : Submodule S H) = 𝔭 ^ n • ⊤ := by
    by_contra hne
    apply hN0min _ ⟨n + 1, rfl⟩ (lt_of_le_of_ne hle hne)
  set N : Submodule S H := 𝔭 ^ n • ⊤ with hN
  have hNle : N ≤ 𝔭 • N := by
    rw [hN, ← Submodule.mul_smul, ← pow_succ', hstab]
  have hNfg : N.FG := (isNoetherian_def.mp hNoeth) N
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔭 N hNfg hNle
  have hrp : r ∉ 𝔭 := by
    intro h
    have : (1 : S) ∈ 𝔭 := by
      have := 𝔭.sub_mem h hr1
      rwa [sub_sub_cancel] at this
    apply Ideal.IsPrime.ne_top' ((Ideal.eq_top_iff_one 𝔭).mpr this)
  have hunit : IsUnit (algebraMap S B r) := IsLocalization.map_units B (⟨r, hrp⟩ : 𝔭.primeCompl)
  obtain ⟨u, hu⟩ := hunit
  refine ⟨n, ?_⟩
  have key : ∀ a : S, a ∈ 𝔭 ^ n → ∀ t : B ⊗[S] H, algebraMap S B a • t = 0 := by
    intro a ha t
    induction t using TensorProduct.inductionOn
    ·
      rename_i b h
      have hah : r • (a • h) = 0 := hr _ (Submodule.smul_mem_smul ha Submodule.mem_top)
      have hb : r • (b * ↑u⁻¹) = b := by
        rw [Algebra.smul_def, ← hu, mul_comm, mul_assoc, Units.inv_mul, mul_one]
      calc
        _ = (algebraMap S B a * b) ⊗ₜ[S] h := by
          rw [TensorProduct.smul_tmul', smul_eq_mul]
        _ = (a • b) ⊗ₜ[S] h := by rw [Algebra.smul_def]
        _ = b ⊗ₜ[S] (a • h) := TensorProduct.smul_tmul a b h
        _ = (r • (b * ↑u⁻¹)) ⊗ₜ[S] (a • h) := by rw [hb]
        _ = (b * ↑u⁻¹) ⊗ₜ[S] (r • (a • h)) := TensorProduct.smul_tmul r _ _
        _ = 0 := by rw [hah, TensorProduct.tmul_zero]
    ·
      rename_i x y hx hy
      rw [smul_add, hx, hy, add_zero]
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 B, ← Ideal.map_pow, eq_bot_iff]
  refine Submodule.smul_le.mpr fun x hx t _ => ?_
  rw [Submodule.mem_bot]
  simp only [Ideal.map, Ideal.span] at hx
  induction hx using Submodule.span_induction
  ·
    rename_i x hx'
    obtain ⟨a, ha, rfl⟩ := hx'
    apply key a ha t
  ·
    apply zero_smul _ _
  ·
    rename_i x y _ _ hx hy
    rw [add_smul, hx, hy, add_zero]
  ·
    rename_i c x _ hx
    rw [smul_eq_mul, mul_smul, hx, smul_zero]


-- created on 2026-10-20
