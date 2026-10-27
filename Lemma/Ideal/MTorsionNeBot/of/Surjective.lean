import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.HeckeGalois_EichlerShimura
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_MTorsionNeBot_of_surjective_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_MTorsionNeBot_of_surjective_of_finite.lean)
-/

private lemma exists_ne_zero_smul_eq_zero_of_pow_smul_eq_zero {𝕋 : Type*} [CommRing 𝕋]
  {N : Type*} [AddCommGroup N] [Module 𝕋 N] (𝔪 : Ideal 𝕋) (n : ℕ) :
  ∀ m : N, m ≠ 0 → (∀ t ∈ 𝔪 ^ n, t • m = 0) → ∃ x : N, x ≠ 0 ∧ ∀ t ∈ 𝔪, t • x = 0 := by
  induction n with
  | zero =>
    intro m hm h
    exfalso
    apply hm
    have h1 : (1 : 𝕋) ∈ 𝔪 ^ 0 := by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    simpa using h 1 h1
  | succ n ih =>
    intro m hm h
    by_cases hn : ∀ t ∈ 𝔪 ^ n, t • m = 0
    · exact ih m hm hn
    ·
      obtain ⟨s, hs, hsm⟩ : ∃ s ∈ 𝔪 ^ n, s • m ≠ 0 := by
        by_contra hc
        exact hn fun t ht => by_contra fun h' => hc ⟨t, ht, h'⟩
      refine ⟨s • m, hsm, fun t ht => ?_⟩
      rw [smul_smul]
      exact h (t * s) (by rw [pow_succ']; exact Ideal.mul_mem_mul ht hs)

private lemma exists_ne_zero_pow_smul_eq_zero_of_surjective {𝕋 : Type*} [CommRing 𝕋]
  {N N'' : Type*} [AddCommGroup N] [Module 𝕋 N] [AddCommGroup N''] [Module 𝕋 N''] (𝔪 : Ideal 𝕋)
  [Finite N] (f : N →ₗ[𝕋] N'') (x₀ : N) (hy0 : f x₀ ≠ 0) (hy : ∀ t ∈ 𝔪, t • f x₀ = 0) :
  ∃ (n : ℕ) (m : N), m ≠ 0 ∧ ∀ t ∈ 𝔪 ^ n, t • m = 0 := by
  haveI : IsArtinian 𝕋 N := isArtinian_of_finite
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := 𝕋) (M := N)
    ⟨fun i => OrderDual.toDual (𝔪 ^ i • (⊤ : Submodule 𝕋 N)),
      fun i j hij => Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)⟩
  have hstab : 𝔪 ^ n • (⊤ : Submodule 𝕋 N) = 𝔪 ^ (n + 1) • (⊤ : Submodule 𝕋 N) :=
    hn (n + 1) (Nat.le_succ n)
  have hle : 𝔪 ^ n • (⊤ : Submodule 𝕋 N) ≤ 𝔪 • (𝔪 ^ n • (⊤ : Submodule 𝕋 N)) := by
    rw [← Submodule.mul_smul, ← pow_succ', ← hstab]
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪
    (𝔪 ^ n • (⊤ : Submodule 𝕋 N)) (IsNoetherian.noetherian _) hle
  refine ⟨n, r • x₀, fun hz => hy0 ?_, fun t ht => ?_⟩
  ·
    have h1 : (r - 1) • f x₀ = 0 := hy (r - 1) hr1
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    rw [← h1, ← map_smul, hz, map_zero]
  ·
    rw [smul_smul, mul_comm, ← smul_smul]
    exact hr (t • x₀) (Submodule.smul_mem_smul ht Submodule.mem_top)
p2m_open_scoped "ModularCurve" in

private lemma ModularCurve.MTorsionNeBot.of_surjective_of_finite_impl {𝕋 : Type*} [CommRing 𝕋]
  {N N'' : Type*} [AddCommGroup N] [Module 𝕋 N] [AddCommGroup N''] [Module 𝕋 N''] (𝔪 : Ideal 𝕋)
  [Finite N] (f : N →ₗ[𝕋] N'') (hf : Function.Surjective f) :
  MTorsionNeBot 𝕋 N'' 𝔪 → MTorsionNeBot 𝕋 N 𝔪 := by
  intro h
  unfold MTorsionNeBot at h ⊢
  rw [Submodule.ne_bot_iff] at h ⊢
  obtain ⟨y, hy, hy0⟩ := h
  rw [Submodule.mem_torsionBySet_iff] at hy
  obtain ⟨x₀, rfl⟩ := hf y
  obtain ⟨n, m, hm0, hm⟩ := exists_ne_zero_pow_smul_eq_zero_of_surjective 𝔪 f x₀ hy0
    (fun t ht => hy ⟨t, ht⟩)
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_smul_eq_zero_of_pow_smul_eq_zero 𝔪 n m hm0 hm
  exact ⟨x, (Submodule.mem_torsionBySet_iff _ _).2 (fun a => hx a.1 a.2), hx0⟩
@[path]
private lemma main
  [CommRing 𝕋]
  {N N'' : Type*} [AddCommGroup N] [Module 𝕋 N] [AddCommGroup N''] [Module 𝕋 N''] [Finite N]
  {𝔪 : Ideal 𝕋}
  {f : N →ₗ[𝕋] N''}
-- given
  (hf : Function.Surjective f) :
-- imply
  MTorsionNeBot 𝕋 N'' 𝔪 → MTorsionNeBot 𝕋 N 𝔪 :=
-- proof
  ModularCurve.MTorsionNeBot.of_surjective_of_finite_impl 𝔪 f hf


-- created on 2026-10-23
