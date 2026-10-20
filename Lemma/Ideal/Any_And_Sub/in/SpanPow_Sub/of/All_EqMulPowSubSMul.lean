import Mathlib
import sympy.Basic


universe u v

/--
[AlgebraicGeometry_AdmissibleAlgebra_exists_smul_eq_sub_of_forall_smul_sub_mem_span_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_AdmissibleAlgebra_exists_smul_eq_sub_of_forall_smul_sub_mem_span_pow.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {G : Type v} [Group G] [Finite G] [MulSemiringAction G R]
  {t : R}
-- given
  (ht : ∀ g : G, g • t = t) (ht0 : ∀ x : R, t * x = 0 → x = 0) {e : ℕ}
  (hH1 : ∀ y : G → R, (∀ g h : G, y (g * h) = g • y h + y g) →
    (∃ (k : ℕ) (z : R), ∀ g : G, t ^ k * y g = g • z - z) → ∃ z : R, ∀ g : G, t ^ e * y g = g • z - z)
  {m : ℕ} (hm : e ≤ m) {x : R} (hx : ∀ g : G, g • x - x ∈ Ideal.span {t ^ m}) :
-- imply
  ∃ w : R, (∀ g : G, g • w = w) ∧ x - w ∈ Ideal.span {t ^ (m - e)} := by
-- proof
  classical
  have htk0 : ∀ (k : ℕ) (x : R), t ^ k * x = 0 → x = 0 := by
    intro k
    induction k
    case zero =>
      intro x hx
      simpa using hx
    case succ k ih =>
      intro x hx
      rw [pow_succ, mul_assoc] at hx
      apply ht0 x (ih _ hx)
  have htk : ∀ (g : G) (k : ℕ), g • t ^ k = t ^ k := fun g k => by rw [smul_pow', ht]
  have hy : ∀ g : G, ∃ y : R, g • x - x = t ^ m * y := fun g => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hx g)
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose y hy using hy
  have hcocycle : ∀ g h : G, y (g * h) = g • y h + y g := by
    intro g h
    have e1 : t ^ m * y (g * h) = t ^ m * (g • y h + y g) := by
      rw [← hy (g * h), mul_add, ← hy g, ← htk g m, ← smul_mul', ← hy h, mul_smul, smul_sub]
      abel
    have : t ^ m * (y (g * h) - (g • y h + y g)) = 0 := by rw [mul_sub, e1, sub_self]
    have := htk0 m _ this
    apply sub_eq_zero.1 this
  obtain ⟨z, hz⟩ := hH1 y hcocycle ⟨m, x, fun g => (hy g).symm⟩
  refine ⟨x - t ^ (m - e) * z, fun g => ?_, ?_⟩
  ·
    have key : g • x - x = t ^ (m - e) * (g • z - z) := by
      rw [hy g, ← hz g, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
    rw [smul_sub, smul_mul', htk]
    linear_combination key
  · apply Ideal.mem_span_singleton'.2 ⟨z, by ring⟩


-- created on 2026-10-20
