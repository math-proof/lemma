import Mathlib
import sympy.Basic


/--
[ModularCurve_atP_toric_exclusion](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_atP_toric_exclusion.lean)
-/
@[main]
private lemma main
  [Group G] [AddCommGroup J] [DistribMulAction G J] [Field k] [AddCommGroup V] [Module k V] [DistribMulAction G V] [SMulCommClass G k V]
  {I : Subgroup G}
  {n : G → ℕ}
  {W : AddSubgroup J}
  {ι : V →+ J}
-- given
  (hmult : ∀ σ ∈ I, ∀ x ∈ W, σ • x = n σ • x)
  (hinj : Function.Injective ι)
  (hequiv : ∀ (g : G) (v : V), ι (g • v) = g • ι v)
  (hsub : ∀ v : V, ι v ∈ W)
  (hrank : Module.finrank k V = 2)
  (hdet : ∀ σ ∈ I, LinearMap.det (DistribMulAction.toLinearMap k V σ) = (n σ : k))
  (hunit : ∀ σ ∈ I, (n σ : k) ≠ 0)
  (hram : ∃ σ ∈ I, (n σ : k) ≠ 1) :
-- imply
  False := by
-- proof
  obtain ⟨σ, hσ, hne⟩ := hram
  apply hne

  have hscalar : ∀ v : V, σ • v = n σ • v := fun v => by
    apply hinj; rw [hequiv, map_nsmul]; exact hmult σ hσ (ι v) (hsub v)
  set A := DistribMulAction.toLinearMap k V σ
  have hAap : ∀ v : V, A v = σ • v := fun v => rfl
  have hsc : ∀ v : V, A v = (n σ : k) • v := fun v => by
    rw [hAap v, hscalar v, Nat.cast_smul_eq_nsmul]
  have hAeq : A = (n σ : k) • (LinearMap.id : V →ₗ[k] V) := by ext v; simp [hsc v]
  have h : (n σ : k) = (n σ : k) ^ 2 := by
    calc (n σ : k) = LinearMap.det A := (hdet σ hσ).symm
      _ = (n σ : k) ^ Module.finrank k V * LinearMap.det (LinearMap.id : V →ₗ[k] V) := by
          rw [hAeq, LinearMap.det_smul]
      _ = (n σ : k) ^ 2 := by rw [hrank, LinearMap.det_id, mul_one]
  have hfactor : (n σ : k) * ((n σ : k) - 1) = 0 := by ring_nf; linear_combination -h
  rcases mul_eq_zero.mp hfactor with h0 | h1
  · exact absurd h0 (hunit σ hσ)
  · exact sub_eq_zero.mp h1


-- created on 2026-10-05
