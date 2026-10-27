import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[LinearMap_finite_and_sum_finrank_eq_of_exact_of_exact_of_exact](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_finite_and_sum_finrank_eq_of_exact_of_exact_of_exact.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] (A B Q : ℕ → Type u) [∀ n, AddCommGroup (A n)] [∀ n, Module k (A n)] [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)] [∀ n, AddCommGroup (Q n)] [∀ n, Module k (Q n)]
  (f : ∀ n, A n →ₗ[k] B n) (g : ∀ n, B n →ₗ[k] Q n) (δ : ∀ n, Q n →ₗ[k] A (n + 1))
  (hfg : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
  (hgδ : ∀ n, LinearMap.range (g n) = LinearMap.ker (δ n))
  (hδf : ∀ n, LinearMap.range (δ n) = LinearMap.ker (f (n + 1)))
  (hA : ∀ n, Module.Finite k (A n)) (hQ : ∀ n, Module.Finite k (Q n))
  (M : ℕ) (hf0 : Function.Injective (f 0)) (hfM : Function.Injective (f M)) :
  -- imply
  (∀ n, Module.Finite k (B n)) ∧ ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n * (Module.finrank k (B n) : ℤ) = ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n * (Module.finrank k (A n) : ℤ) + ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n * (Module.finrank k (Q n) : ℤ) := by
  -- proof
  have hB : ∀ n, Module.Finite k (B n) := by
    intro n
    let _ := hA n
    let _ := hQ n
    rw [Module.finite_def]
    apply Submodule.fg_of_fg_map_of_fg_inf_ker (g n)
    ·
      rw [Submodule.map_top]
      apply IsNoetherian.noetherian _
    ·
      rw [top_inf_eq, ← hfg n, LinearMap.range_eq_map]
      apply Module.Finite.fg_top.map _
  refine ⟨hB, ?_⟩
  have key : ∀ n, (Module.finrank k (A n) : ℤ) - Module.finrank k (B n) + Module.finrank k (Q n) = Module.finrank k (LinearMap.ker (f n)) + Module.finrank k (LinearMap.ker (f (n + 1))) := by
    intro n
    let _ := hA n
    let _ := hQ n
    let _ := hB n
    let _ := hA (n + 1)
    have h1 := LinearMap.finrank_range_add_finrank_ker (f n)
    have h2 := LinearMap.finrank_range_add_finrank_ker (g n)
    have h3 := LinearMap.finrank_range_add_finrank_ker (δ n)
    rw [← hfg n] at h2
    rw [← hgδ n] at h3
    have h4 : Module.finrank k (LinearMap.range (δ n)) = Module.finrank k (LinearMap.ker (f (n + 1))) := by
      rw [hδf n]
    omega
  have tel : ∀ L : ℕ, ∑ n ∈ Finset.range L, (-1 : ℤ) ^ n * ((Module.finrank k (A n) : ℤ) - Module.finrank k (B n) + Module.finrank k (Q n)) = (Module.finrank k (LinearMap.ker (f 0)) : ℤ) - (-1 : ℤ) ^ L * Module.finrank k (LinearMap.ker (f L)) := by
    intro L
    induction L
    ·
      simp
    ·
      rename_i L ih
      rw [Finset.sum_range_succ, ih, key L, pow_succ]
      ring
  have hk0 : Module.finrank k (LinearMap.ker (f 0)) = 0 := by
    rw [LinearMap.ker_eq_bot.mpr hf0, finrank_bot]
  have hkM : Module.finrank k (LinearMap.ker (f M)) = 0 := by
    rw [LinearMap.ker_eq_bot.mpr hfM, finrank_bot]
  have h := tel M
  rw [hk0, hkM] at h
  simp only [Nat.cast_zero, mul_zero, sub_zero] at h
  have e : ∀ n, (-1 : ℤ) ^ n * (Module.finrank k (B n) : ℤ) = ((-1 : ℤ) ^ n * (Module.finrank k (A n) : ℤ) + (-1 : ℤ) ^ n * (Module.finrank k (Q n) : ℤ)) - (-1 : ℤ) ^ n * ((Module.finrank k (A n) : ℤ) - Module.finrank k (B n) + Module.finrank k (Q n)) := by
    intro n; ring
  rw [Finset.sum_congr rfl (fun n _ => e n), Finset.sum_sub_distrib, Finset.sum_add_distrib, h, sub_zero]


-- created on 2026-10-20
