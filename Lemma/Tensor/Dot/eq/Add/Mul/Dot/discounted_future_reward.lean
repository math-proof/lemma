import sympy.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic


@[main]
private lemma main
  {γ : ℝ}
  {r : ℕ → ℝ}
  {t : ℕ}
-- given
  (h : Summable (fun i : ℕ => γ ^ i * r (i + t))) :
-- imply
  (∑' i : ℕ, γ ^ i * r (i + t)) = r t + γ * (∑' i : ℕ, γ ^ i * r (i + t + 1)) := by
-- proof
  let g : ℕ → ℝ := fun i => γ ^ i * r (i + t + 1)
  have hstep : ∀ i : ℕ, γ ^ (i + 1) * r (i + 1 + t) = γ * g i := by
    intro i
    have hti : i + 1 + t = i + t + 1 := by omega
    simp [g, hti, pow_succ, mul_assoc]; ring
  have hsucc : Summable (fun i : ℕ => γ * g i) := by
    have heq : (fun i : ℕ => γ * g i) = (fun i : ℕ => γ ^ i * r (i + t)) ∘ Nat.succ := by
      funext i
      exact (hstep i).symm
    rw [heq]
    exact h.comp_injective Nat.succ_injective
  have h₂ : Summable g := by
    by_cases hγ : γ = 0
    · subst hγ
      have hfin : Set.Finite (Function.support g) := by
        apply Set.Finite.subset (Set.finite_singleton 0)
        intro x hx
        simp only [Function.mem_support, Ne, g] at hx
        by_contra hnz
        have : (0 : ℝ) ^ x = 0 := zero_pow hnz
        rw [this] at hx; simp at hx
      exact summable_of_hasFiniteSupport hfin
    · have h₃ : g = fun i : ℕ => γ⁻¹ * (γ * g i) := by
        funext i
        field_simp
      rw [h₃]
      exact hsucc.mul_left γ⁻¹
  have h₁ : (∑' i : ℕ, γ ^ i * r (i + t)) = r t + ∑' i : ℕ, γ * g i := by
    rw [h.tsum_eq_zero_add]
    have ha : (γ ^ 0 * r (0 + t)) = r t := by simp [pow_zero]
    have hb : (fun i : ℕ => γ ^ (i + 1) * r (i + 1 + t)) = fun i : ℕ => γ * g i := by
      funext i; exact hstep i
    rw [ha, hb]
  rw [h₁, h₂.tsum_mul_left γ]


-- created on 2026-09-26
