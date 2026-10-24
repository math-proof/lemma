import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[HopfAlgebra_normOneTorus_quotient_nTorsion_points_of_powerPair](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_normOneTorus_quotient_nTorsion_points_of_powerPair.lean)
-/
@[path]
private lemma main
  {K : Type} [Field K] [CharZero K]
  {n : ℕ} [Fact n.Prime]
  {B₀ : Type} [CommRing B₀] [Algebra K B₀]
  {A : Type} [CommRing A] [Algebra K A]
  {c : K}
  {δ : AlgebraicClosure K}
  {u₀ v₀ P Q : B₀}
  {u' v' : A}
  {π : B₀ →ₐ[K] A}
  -- given
  (hc : c ≠ 0)
  (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
  (hlift₀ : ∀ (w z : AlgebraicClosure K), w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 → ∃! g : B₀ →ₐ[K] AlgebraicClosure K, g u₀ = w ∧ g v₀ = z)
  (hpow : ∀ f : B₀ →ₐ[K] AlgebraicClosure K, f P + f Q * δ = (f u₀ + f v₀ * δ) ^ n ∧ f P - f Q * δ = (f u₀ - f v₀ * δ) ^ n)
  (hπu : π u₀ = u')
  (hπv : π v₀ = v')
  (hπP : π P = 1)
  (hπQ : π Q = 0)
  (hfact : ∀ g : B₀ →ₐ[K] AlgebraicClosure K, g P = 1 → g Q = 0 → ∃ f : A →ₐ[K] AlgebraicClosure K, f.comp π = g)
  (hgen' : Algebra.adjoin K {u', v'} = ⊤) :
  -- imply
  (∀ f : A →ₐ[K] AlgebraicClosure K, (f u' + f v' * δ) ^ n = 1) ∧ (∀ (w z : AlgebraicClosure K), w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 → (w + z * δ) ^ n = 1 → ∃! f : A →ₐ[K] AlgebraicClosure K, f u' = w ∧ f v' = z) := by
  -- proof
  have hδ0 : δ ≠ 0 := by
    intro h
    apply hc
    have := hδ
    rw [h, mul_zero] at this
    apply FaithfulSMul.algebraMap_injective K (AlgebraicClosure K) (this.symm.trans (map_zero _).symm)
  have huniq : ∀ (f₁ f₂ : A →ₐ[K] AlgebraicClosure K), f₁ u' = f₂ u' → f₁ v' = f₂ v' → f₁ = f₂ := by
    intro f₁ f₂ hu hv
    apply AlgHom.ext
    intro a
    have ha : a ∈ Algebra.adjoin K {u', v'} := hgen' ▸ Algebra.mem_top
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    ·
      intro x hx
      obtain rfl | rfl := hx
      · apply hu
      · apply hv
    ·
      intro r
      simp [AlgHom.commutes]
    ·
      intro x y _ _ hx hy
      simp [map_add, hx, hy]
    ·
      intro x y _ _ hx hy
      simp [map_mul, hx, hy]
  refine ⟨?_, ?_⟩
  ·
    intro f
    have h := (hpow (f.comp π)).1
    simp only [AlgHom.comp_apply, hπP, hπQ, hπu, hπv, map_one, map_zero, zero_mul, add_zero] at h
    apply h.symm
  ·
    intro w z hrel hn1
    obtain ⟨g, ⟨hgu, hgv⟩, -⟩ := hlift₀ w z hrel
    have hpg := hpow g
    rw [hgu, hgv] at hpg
    obtain ⟨hp1, hp2⟩ := hpg
    have hprod : (w + z * δ) * (w - z * δ) = 1 := by
      have : w ^ 2 - z ^ 2 * (δ * δ) = 1 := by
        rw [hδ]
        linear_combination hrel
      linear_combination this
    have hn2 : (w - z * δ) ^ n = 1 := by
      have hunit : (w - z * δ) = (w + z * δ)⁻¹ := eq_inv_of_mul_eq_one_right hprod
      rw [hunit, inv_pow, hn1, inv_one]
    rw [hn1] at hp1
    rw [hn2] at hp2
    have hgP : g P = 1 := by
      have h2 : (2 : AlgebraicClosure K) * g P = 2 := by
        linear_combination hp1 + hp2
      have h2ne : (2 : AlgebraicClosure K) ≠ 0 := two_ne_zero
      field_simp [h2ne] at h2
      apply h2
    have hgQ : g Q = 0 := by
      have h2 : (2 : AlgebraicClosure K) * (g Q * δ) = 0 := by
        linear_combination hp1 - hp2
      have h2ne : (2 : AlgebraicClosure K) ≠ 0 := two_ne_zero
      obtain h | h := Iff.mp mul_eq_zero h2
      · apply absurd h h2ne
      ·
        obtain h' | h' := Iff.mp mul_eq_zero h
        · apply h'
        · apply absurd h' hδ0
    obtain ⟨f, hfπ⟩ := hfact g hgP hgQ
    have hfu : f u' = w := by
      rw [← hπu, ← AlgHom.comp_apply, hfπ, hgu]
    have hfv : f v' = z := by
      rw [← hπv, ← AlgHom.comp_apply, hfπ, hgv]
    refine ⟨f, ⟨hfu, hfv⟩, ?_⟩
    intro f' ⟨hf'u, hf'v⟩
    apply huniq f' f (hf'u.trans hfu.symm) (hf'v.trans hfv.symm)


-- created on 2026-10-20
