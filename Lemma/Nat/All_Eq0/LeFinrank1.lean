import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[LinearMap_finrank_iInf_eigenspace_le_one_of_coeff_hecke_law](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_finrank_iInf_eigenspace_le_one_of_coeff_hecke_law.lean)
-/
@[path]
private lemma main
  [Field K] [AddCommGroup V] [Module K V]
  (a : ℕ → V →ₗ[K] K)
  (hinj : ∀ v : V, (∀ n : ℕ, 1 ≤ n → a n v = 0) → v = 0)
  (T : ℕ → V →ₗ[K] V) (c : ℕ → K)
  (hlaw : ∀ ℓ : ℕ, ℓ.Prime → ∀ n : ℕ, 1 ≤ n → ∀ v : V, a n (T ℓ v) = a (n * ℓ) v + (if ℓ ∣ n then c ℓ * a (n / ℓ) v else 0))
  (μ : ℕ → K) :
  -- imply
  (∀ v ∈ ⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (T ℓ) (μ ℓ), a 1 v = 0 → v = 0) ∧ Module.finrank K ↥(⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (T ℓ) (μ ℓ)) ≤ 1 := by
  -- proof
  classical
  set W : Submodule K V := ⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (T ℓ) (μ ℓ) with hW
  have hmem : ∀ v ∈ W, ∀ ℓ : ℕ, ℓ.Prime → T ℓ v = μ ℓ • v := by
    intro v hv ℓ hℓ
    have h1 : v ∈ Module.End.eigenspace (T ℓ) (μ ℓ) := by
      have := (Submodule.mem_iInf _).1 hv ℓ
      apply (Submodule.mem_iInf _).1 this hℓ
    refine Module.End.mem_eigenspace_iff.1 h1
  have key : ∀ v ∈ W, a 1 v = 0 → ∀ n : ℕ, 1 ≤ n → a n v = 0 := by
    intro v hv h1 n
    induction n using Nat.strong_induction_on
    ·
      rename_i n ih
      intro hn
      if hn1 : n = 1 then
        subst hn1
        apply h1
      else
        have hn2 : 2 ≤ n := by omega
        obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 from hn1)
        obtain ⟨m, rfl⟩ := hℓn
        have hℓpos : 0 < ℓ := hℓ.pos
        have hm1 : 1 ≤ m := by
          obtain h | h := Nat.eq_zero_or_pos m
          ·
            subst h
            simp at hn
          ·
            apply h
        have hmlt : m < ℓ * m := by
          have := hℓ.two_le
          nlinarith
        have ham : a m v = 0 := ih m hmlt hm1
        have hlaw' := hlaw ℓ hℓ m hm1 v
        rw [hmem v hv ℓ hℓ, LinearMap.map_smul, smul_eq_mul, ham, mul_zero] at hlaw'
        have hite : (if ℓ ∣ m then c ℓ * a (m / ℓ) v else 0) = 0 := by
          split_ifs with hdiv
          ·
            obtain ⟨r, rfl⟩ := hdiv
            have hr1 : 1 ≤ r := by
              obtain h | h := Nat.eq_zero_or_pos r
              ·
                subst h
                simp at hm1
              ·
                apply h
            have hrlt : r < ℓ * (ℓ * r) := by
              have := hℓ.two_le
              nlinarith
            rw [Nat.mul_div_cancel_left r hℓpos, ih r hrlt hr1, mul_zero]
          ·
            rfl
        rw [hite, add_zero] at hlaw'
        rw [mul_comm] at hlaw'
        apply hlaw'.symm
  have hi : ∀ v ∈ W, a 1 v = 0 → v = 0 := fun v hv h1 => hinj v (key v hv h1)
  refine ⟨hi, ?_⟩
  let f : W →ₗ[K] K := (a 1).domRestrict W
  have hf : Function.Injective f := by
    intro x y hxy
    have : a 1 (x - y : W) = 0 := by
      change a 1 ((x : V) - (y : V)) = 0
      rw [map_sub]
      apply sub_eq_zero.2 hxy
    have h0 := hi _ (x - y).2 this
    refine Subtype.ext (sub_eq_zero.1 (by exact_mod_cast h0))
  calc
    _ ≤ Module.finrank K K := LinearMap.finrank_le_finrank_of_injective hf
    _ = 1 := Module.finrank_self K


-- created on 2026-10-20
